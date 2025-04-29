#!/usr/bin/python

## 	@package anasyn
# 	Syntactical Analyser package. 
#

import os
import sys, argparse, re
import logging

import analex

logger = logging.getLogger('anasyn')

DEBUG = False
LOGGING_LEVEL = logging.DEBUG

########################################################################	
# Global variables
########################################################################
identifierTable=[]
flagParameter=False
flagDependance=[]
NOM=0 #Correspond à l'indice du nom de l'identificateur dans une ligne de la table des identificateurs
CLASS=1 #Correspond à l'indice de la classe (LOC ou PARAMETER) de l'identificateur dans une ligne de la table des identificateurs
DEPENDANCE=2 #Correspond à l'indice de la dépendance de l'identificateur dans une ligne de la table des identificateurs
TYPE=3 #Correspond à l'indice du type (integer ou boolean ou FONCTION ou PROCEDURE) de l'identificateur dans une ligne de la table des identificateurs
ADRESSE=4 #Correspond à l'indice de l'adresse de l'identificateur dans une ligne de la table des identificateurs
PLACE=5 #Correspond à l'indice de la place que prend la fonction/procédure de l'identificateur dans une ligne de la table des identificateurs


codeGenerator = [] # Variable dans laquelle on stocke les instructions générées. Ce sont ces dernières qui seront envoyées à la VM
Line = 0 # Variable qui contient le numéro de la ligne suivante à écrire
nb_var = 0 # Nombre de variables dans une partie du programme (nombre de déclarations)
procEnCours = [] # Liste des procédures et fonctions dans l'ordre du traitement
DebutFinProcFunc = [] # Tableau qui contient les noms des procédures (hors programme principal) et fonctions ainsi que le numéro de la ligne où elles commencent et la ligne suivant leur retour ainsi que leur type
nb_tze = 1 # Numéro du tze en cours de traitement
tzeEnCours = {} # Dictionnaire ressençant les tze en cours de traitement
flagIF = []	# Liste des if avec la présence ou non d'un else
exp = [] # Liste qui contient les expressions à traiter
lstVariablesAppelees = [] # Liste qui contient les variables (à calculer) utilisées dans un appel de procédure ou de fonction



params = [] # liste du nombre de paramêtres analysés (change à chaque analyse de fonction/procédure)
left_type = None # type de gauche dans les expression, pour les testes de typage.
ident = None # identificateur utilisé dans les vérifications sémantiques
function = None # identificateur de la fonction/procedure utilisée 

class AnaSynException(Exception):
	def __init__(self, value):
		self.value = value
	def __str__(self):
		return repr(self.value)



########################################################################				 	
#### Code Generation
########################################################################	

def remplacer(instruction, ligne): # Lorsque les instructions tra et tze sont générées, on ne connait pas encore les adresses de destination. Ce programme permet de leur affecter la bonne valeur 
	global codeGenerator
	for i in range (len(codeGenerator)) :
		if codeGenerator[i] == instruction :
			if instruction[0:3] == "tra" and instruction[3:7] != "Stat": # On ne remplace pas les traStat
				codeGenerator[i] = "tra(" + str(ligne) + ")"
			if instruction[0:3] == "tze":
				codeGenerator[i] = "tze(" + str(ligne) + ")"

# On renvoie la ligne de début de la procédure ou de la fonction
def trouveDebutProcFunc(name):
	global DebutFinProcFunc
	for (Nom, LigneDebut, LigneFin) in DebutFinProcFunc:
		if Nom == name :
			return LigneDebut
	raise AnaSynException("ERROR <trouveDebutProcFunc>: Procedure or function not found!")

# Lorsque l'on a terminer la déclaration d'une fonction ou d'une procédure, on met à jour sa ligne de fin
def modifieFinProcFunc(nom, ligne):
	global DebutFinProcFunc
	for i in range (len(DebutFinProcFunc)):
		if DebutFinProcFunc[i][0] == nom :
			DebutFinProcFunc[i][2] = ligne
			remplacer("tra(" + nom + ")", ligne) # On remplace le tra(nomProcFonc) par la valeur de fin
			return
	raise AnaSynException("ERROR <modifieFinProcFunc>: Procedure or function not found!")

# On regarde si str est une constante. Si c'est le cas, on renvoie True si c'est une variable on renvoie False
def is_not_var(str) :
	if (str[0] >= "0" and str[0] <= "9") or str[0:4] == "True" or str[0:5] == "False":
		return True
	return False

# On calcule les paramètres d'une fonction ou d'une procédure
def empileParam(dependance):
	global exp, lstVariablesAppelees
	for (n_exp) in lstVariablesAppelees :
		calcul_expression(n_exp, dependance)
	lstVariablesAppelees = []
	exp = []
	
#Si str est un entier on renvoie True, sinon on renvoie False (il s'agit d'un booléen)
def is_int(str) :
    if str[0] >= "0" and str[0] <= "9" :
        return True
    return False



# On récupère la prochaine expression entre parenthèses
def exp_par (exp, indice) :
    compteur = 1
    nouvelle_exp = []
    while compteur != 0 :
        indice += 1
        if exp[indice] == "(" :
            compteur += 1
        if exp[indice] == ")" :
            compteur -= 1
        nouvelle_exp += [exp[indice]]
    nouvelle_exp.pop()
    return nouvelle_exp

# On regarde si opérateur actuel est prioritaire par rapport à l'opérateur suivant. 
# Si c'est le cas, on renvoie True ainsi que la localisation de l'opérateur suivant
# Sinon on renvoie False ainsi que le prochain opérateur prioritaire
def prioritaire (exp, indice) :
    next_indice = next_ind(exp, indice + 1)
    if est_prio(exp[indice], next_indice):
        return True, next_indice
    else :
        return False, next_prio(exp, indice)

# On renvoie l'adresse du prochain opérateur (en sautant les expressions entre parenthèses)
def next_ind(exp, indice):
    for i in range (indice, len(exp)):
        if exp[i] in ["mult()", "div()", "add()", "sous()"]:
            return i
        elif exp[i] in ['inf()','infeg()','sup()','supeg()','egal()','diff()','et()','ou()']:
            return i
        elif exp[i] == "(":
            i = saute_par(exp, i)
    return -1

# On renvoie l'adresse di prochain opérateur prioritaire
def next_prio (exp, indice):
    i = indice
    next_indice = next_ind(exp, indice + 1)
    while (not est_prio(exp[i], exp[next_indice]) and next_indice != -1) :
        next_indice = next_ind(exp, next_indice + 1)
    return next_indice

# On compare la priorité de deux opérateurs (en sachant que l'opérateur 1 est lu avant l'opérateur 2 dans l'expression)
def est_prio (op1, op2):
    if op2 in ['inf()','infeg()','sup()','supeg()','egal()','diff()'] and op1 not in ['et()','ou()']:
        return True
    elif op1 in ["mult()", "div()"]:
        return True
    elif op1 in ["add()", "sous()"] and op2 in ["add()", "sous()"]:
        return True
    else :
        return False

# On renvoie l'adresse de l'instruction située après la parenthèse fermante
def saute_par(exp, indice):
    compteur = 1 # On commence juste après la parenthèse lue
    while compteur != 0 :
        indice += 1
        if exp[indice] == "(" :
            compteur += 1
        if exp[indice] == ")" :
            compteur -= 1
    return indice

# On génère le code réalisant les calculs
# C'est ici que sont traitées les expressions
def calcul_expression(nouvelle_exp,dependance):
    i = 0
    Is_not = False
    Is_moins = False
    operateur = ['add()','sous()','mult()','div()']
    operateur_logique = ['inf()','infeg()','sup()','supeg()','egal()','diff()','et()','ou()']
    Flag_operateur =''
    Flag_operateur_logique =''
    while i < len(nouvelle_exp) :
        if nouvelle_exp[i] == 'non()' :
            Is_not = True
            i +=1
        elif nouvelle_exp[i] == 'moins()' :
            Is_moins = True
            i +=1
        elif nouvelle_exp[i] in operateur :
            priorité = prioritaire(nouvelle_exp,i)
            if Flag_operateur != '' :
                    if priorité[1] == -1 :
                        liste = nouvelle_exp[i+1:]
                    else :
                        liste = nouvelle_exp[i+1:priorité[1]]
                    calcul_expression(liste,dependance)
                    generate_code(nouvelle_exp[i])
                    generate_code(Flag_operateur)
                    Flag_operateur =''
                    i += len(nouvelle_exp[i+1:priorité[1]])+1
            elif priorité[0] :
                if priorité[1] == -1 :
                    liste = nouvelle_exp[i+1:]
                else :
                    liste = nouvelle_exp[i+1:priorité[1]]
                calcul_expression(liste,dependance)
                generate_code(nouvelle_exp[i])
                i += len(liste)+1
            else :
                Flag_operateur = nouvelle_exp[i]
                i += 1
        elif nouvelle_exp[i] in operateur_logique :
            if Is_not :
                generate_code('non()')
                Is_not = False
            priorité = prioritaire(nouvelle_exp,i)
            if Flag_operateur_logique != '' :
                if priorité[1] == -1 :
                    liste = nouvelle_exp[i+1:]
                else :
                    liste = nouvelle_exp[i+1:priorité[1]]
                calcul_expression(liste,dependance)
                generate_code(nouvelle_exp[i])
                generate_code(Flag_operateur_logique)
                Flag_operateur_logique =''
                i += len(liste)+1
            elif priorité[0] :
                if priorité[1] == -1 :
                    liste = nouvelle_exp[i+1:]
                else :
                    liste = nouvelle_exp[i+1:priorité[1]]
                calcul_expression(liste,dependance)
                generate_code(nouvelle_exp[i])
                i += len(liste)+1
            else :
                Flag_operateur_logique = nouvelle_exp[i]
                i += 1
        elif nouvelle_exp[i] == '(' :
            ss_exp = exp_par(nouvelle_exp,i)
            calcul_expression(ss_exp,dependance)
            if Is_not :
                generate_code('non()')
                Is_not = False
            if Is_moins :
                generate_code('moins()')
                Is_moins = False
            i += len(ss_exp)+2
        else :
            val = str(nouvelle_exp[i])
            if is_param(nouvelle_exp[i],dependance) :
                addr = adresse(val,dependance)
                generate_code("empilerParam("+ str(addr) +")")
                generate_code("valeurPile()")
            elif is_not_var(val):
                if val == "True" :
                    val = "1"
                elif val == "False" :
                    val = "0" 
                generate_code("empiler("+ val + ")")
                if Is_not :
                    generate_code('non()')
                    Is_not = False  
                if Is_moins :
                    generate_code('moins()')
                    Is_moins = False
            else :
                addr = adresse(nouvelle_exp[i],dependance)
                generate_code("empilerAd("+ str(addr) +")")
                generate_code("valeurPile()")
            i +=1
    if Is_not :
        generate_code('non()')
    if Is_moins :
        generate_code('moins()')
    if Flag_operateur != '' :
        generate_code(Flag_operateur)
    if Flag_operateur_logique != '' :
        generate_code(Flag_operateur_logique)
            


# C'est ici que l'on intercepte les génération d'instructions
def generate_code(instruction):
	global codeGenerator, Line, nb_var, DebutFinProcFunc, procEnCours, nb_tze, tzeEnCour, lstVariablesAppelees, flagIF, exp # On récupère les variables globales
	final_instruction = instruction # Par défaut, on récupère l'instruction telle quelle. Si aucun if ne match son cas, on l'ajoute telle quelle
	nb_line = 1 # Par défaut, on avance donc d'une ligne
	if instruction[0:9] == "debutProg": # Traitement du début du programme
		final_instruction = "debutProg()" 
		nom = instruction[9:]
		procEnCours += [nom] # On ajoute le nom du programme principal à la liste des procédures/fonctions en cours

	if instruction[0:4] == "Name": # Traitement du nom d'une nouvelle procédure ou fonction
		nom = instruction[4:]
		DebutFinProcFunc += [[nom, Line + 2, -1]] # On ajoute le nom de la procédure et le numéro de la ligne où elle commence
		final_instruction = "tra(" + nom + ")" # On écrit tra(nom_de_la_procédure/fonction) en attendant de connaître la ligne de fin
		procEnCours += [nom] # On ajoute le nom de la procédure/fonction en cours

	# On calcul la valeur de l'expression en cours pour pouvoir l'affecter
	if instruction == "affectation()":
		nomProcEnCours = procEnCours[-1]
		calcul_expression(exp, nomProcEnCours)

	# On a fini de déclarer des variables, on leur réserve la place nécessaire
	if instruction == "finDeclaVar":
		if nb_var != 0: # On vérie que l'on a bien des variables à réserver
			final_instruction = "reserver(" + str(nb_var) + ")"
			nb_var = 0
		else :
			final_instruction = "ignore" # Ecrire reserver(0) ne sert à rien
	
	# On appelle une variable
	if(instruction[0:8] == "appelVar"):
		nomProcEnCours = procEnCours[-1]
		nomVar = instruction[8:]
		addr = adresse(nomVar, nomProcEnCours)
		final_instruction = "empilerAd(" + str(addr) + ")"
		
	# On démarre une boucle ou un if
	if instruction == "tze":
		tzeEnCours[nb_tze] = Line + 1
		calcul_expression(exp, procEnCours[-1])
		final_instruction = "tze(tze" + str(nb_tze) + ")"
		nb_tze += 1
	
	# On termine une boucle ou un if
	if instruction[0:6] == "endtze":
		typeboucle = instruction[6:]
		nb_tze -= 1
		if typeboucle[0:5] == "while":
			remplacer("tze(tze" + str(nb_tze) + ")", Line + 2)
			final_instruction = "tra(" + str(tzeEnCours.get(nb_tze)) + ")"
		
		elif typeboucle[0:2] == "if": # Dans le cas d'un if on doit regarder s'il y a un else ou non et garder cela en mémoire pour la terminaison du if
			
			if typeboucle[2:] == "else":
				flagIF.append([flagIF.pop()[0], True]) # Mise à jour du flagIF (ce if possède un else)
				remplacer("tze(tze" + str(nb_tze) + ")", Line + 2)
				final_instruction = "tra(tra" + str(nb_tze) + ")"				
				nb_tze += 1 # On reste dans le même tze en fait

			elif typeboucle[2:] == "end":
				flag = flagIF.pop()[1]
				final_instruction = "ignore"
				if flag == False:
					remplacer("tze(tze" + str(nb_tze) + ")", Line + 2)
				else :
					remplacer("tra(tra" + str(nb_tze) + ")", Line + 1)
			else:
				raise AnaSynException("ERROR <generate_code>: Unknown loop (if) type!")
		else :
			raise AnaSynException("ERROR <generate_code>: Unknown loop type!")
		# Les raise AnaSynException permettent de s'assurer que le code du compilateur est bon, et non pas que le code à compiler l'est

	if instruction == "tra": # If
		remplacer("tra(tra" + str(nb_tze) + ")", Line + 1)
		final_instruction = "ignore"

	# On appelle une procédure ou une fonction	
	if instruction[0:13] == "appelProcFonc":
		final_instruction = []
		generate_code("reserverBloc()")
		nbParam = len(lstVariablesAppelees)
		
		nomProcEnCours = procEnCours[-1]
		empileParam(nomProcEnCours)

		nom = instruction[13:]
		addrProcFunc = trouveDebutProcFunc(nom)
		final_instruction += ["traStat(" + str(addrProcFunc) + "," + str(nbParam) + ")"]

	# On affecte une valeur à une variable
	if instruction[0:3] == "get":
		nom = instruction[3:]
		final_instruction = []
		nomProcEnCours = procEnCours[-1]
		final_instruction += ["empilerAd(" + str(adresse(nom, nomProcEnCours)) + ")"]
		final_instruction += ["get()"]
		nb_line = 2

	# On calcule une expression pour l'afficher ensuite
	if instruction == "put":
		nomProcEnCours = procEnCours[-1]
		calcul_expression(exp, nomProcEnCours)
		final_instruction = "put()"
	
	# On sort d'une procédure. On met donc à jour sa ligne de fin.
	if instruction == "retourProc()": # On ne peut sortir d'une procédure que par un endroit
		nomProcEnCours = procEnCours[-1]
		procEnCours.pop()
		modifieFinProcFunc(nomProcEnCours, Line + 2) # On met à jour la ligne de fin de la procédure et on remplace le tra(nomProc) par la valeur de fin

	# On a un retour de fonction (on ne sort pas de la fonction systématiquement)
	if instruction == "retourFonct()": # On ne sort pas de la fonction
		nomProcEnCours = procEnCours[-1]
		calcul_expression(exp, nomProcEnCours)

	 # On sort de la fonction. On met donc à jour sa ligne de fin.
	if instruction == "sortieFonction": # On sort de la fonction
		final_instruction = "ignore"
		nomProcEnCours = procEnCours[-1]
		modifieFinProcFunc(nomProcEnCours, Line + 1) # On met à jour la ligne de fin de la fonction et on remplace le tra(nomFonc) par la valeur de fin
		procEnCours.pop()

	# Si une des section précédente ne génère pas de code alors on ne rajoute rien dans le code généré (pas d'auugmentation de la ligne non plus)
	if final_instruction != "ignore":
		# On met à jour le code généré (il peut y avoir plusieurs instructions générées en une seule fois)
		if type(final_instruction) == list:
			for instruction in final_instruction:
				codeGenerator += [instruction]
		else:
			codeGenerator += [final_instruction]
		Line += nb_line


########################################################################				 	
#### Semantic Verification
########################################################################	

# Fonction vérifiant si l'identificateur est bien défini dans la table dans la fonction où il est appelé => identifier
def is_declared(identifier, scope):
    for entry in identifierTable:
		# On cherche dans la table des identificateurs si identifier est présent, avec le scope actuel.
		# le deuxième teste est là pour gérer la récursivité
        if (entry[NOM] == identifier and entry[DEPENDANCE] == scope) or (identifier == scope == entry[NOM]):
            return True # On renvoit True dès qu'on le trouve
    return False # False si pas trouvé

# Fonction qui vérifie si une fonction (ou une procedure) existe => identifier
	# Si c'est le cas, vérifie que le nombres de paramètres indiqués est valide => params
	# Renvois des erreurs si les conditions ne sont pas remplies  
def check_function_call(identifier, params, scope):
	for entry in identifierTable:
		# On vérifie si on trouve identifier dans la table, avec le bon scope et si c'est bien une fonction ou une procedure
		# le deuxième teste du or est là pour gérer la récursivité
		if entry[TYPE] in ("FONCTION", "PROCEDURE") and ((entry[NOM] == identifier and entry[DEPENDANCE] == scope) or (identifier == scope == entry[NOM])):
			expected_params = entry[PLACE]  # On récupère le nombre de paramètre voulu
			if params[-1] == expected_params or (expected_params == '' and params[-1] == 0): # On vérifie que le nombre de paramêtres entrés est valide
				return True # On renvoit true dès qu'on le trouve
			else : 
				# Soulève une erreur si c'est pas le cas
				logger.error(f"Incorrect number of parameters for {identifier}: expected {expected_params}, got {params[-1]}")
				raise AnaSynException(f"Incorrect number of parameters for {identifier}: expected {expected_params}, got {params[-1]}")
	# Soulève une erreur si fonction/procedure non trouvée
	logger.error(f"Call to undeclared function/procedure: {identifier}")
	raise AnaSynException(f"Call to undeclared function/procedure: {identifier}")

# Fonction renvoyant le type de l'identificateur (variable, ...) => identifier
def get_type(identifier, scope):
    for entry in identifierTable:
		# On cherche identifier dans toute la table
        if entry[NOM] == identifier and entry[DEPENDANCE] == scope:
            return entry[TYPE] # retourne son type dès qu'identifier est trouvé
    return None # retourne None par défaut si identificateur non trouvé

# Procédure vérifiant que 2 types sont les mêmes (autrement dit que actual_type corresponde bien à expected_type) 
def check_type(expected_type, actual_type, operation):
    if expected_type != actual_type:
		# On renvoi une erreur si les deux types entrés en paramètre ne sont pas les mêmes
		# On utilise operation pour faciliter le debug. Permet de savoir quelle opération pose problème
        logger.error(f"Type error in {operation}: expected {expected_type}, got {actual_type}")
        raise AnaSynException(f"Type error in {operation}: expected {expected_type}, got {actual_type}")
		


########################################################################				 	
#### Syntactical Diagrams
########################################################################

# Dans la suite, on va appeler generate_code dans les moments opportuns pour générer les instructions nécessaires à la VM
# Parfois, des variables seront modifiées
# L'analyse sémantique a également lieu ici
def program(lexical_analyser):
	global codeGenerator, Line # On initialise les variables globales
	codeGenerator = []
	Line = 0
	specifProgPrinc(lexical_analyser)
	if not lexical_analyser.isKeyword("is"):
		#ERROR
		logger.debug("ERROR <program>: 'is' keyword expected!")
		raise AnaSynException("ERROR <program>: 'is' keyword expected!")
	lexical_analyser.acceptKeyword("is")
	corpsProgPrinc(lexical_analyser)
	
def specifProgPrinc(lexical_analyser):
	global ident
	if not lexical_analyser.isKeyword("procedure"):
		#ERROR
		logger.debug("ERROR <specifProgPrinc>: 'procedure' keyword expected!")
		raise AnaSynException("ERROR <specifProgPrinc>: 'procedure' keyword expected!")
	lexical_analyser.acceptKeyword("procedure")
	ident = lexical_analyser.acceptIdentifier()
	logger.debug("Name of program : "+ident)
	generate_code("debutProg" + ident)

	#Entrer le nom de la procédure dans la table des identificateurs
	identifierTable.append([ident,"NONE","NONE","PROCEDURE","",""])
	#Empiler le nom dans le flag dépendance
	flagDependance.append(ident)
	
def corpsProgPrinc(lexical_analyser):
	if not lexical_analyser.isKeyword("begin"):
		logger.debug("Parsing declarations")
		partieDecla(lexical_analyser)
		logger.debug("End of declarations")
	#ERROR
	if not lexical_analyser.isKeyword("begin"):
		logger.error("ERROR Keyword 'begin' expected!")
		raise AnaSynException("Keyword 'begin' expected!")
	lexical_analyser.acceptKeyword("begin")

	if not lexical_analyser.isKeyword("end"):
		logger.debug("Parsing instructions")
		suiteInstr(lexical_analyser)
		logger.debug("End of instructions")
	#ERROR
	if not lexical_analyser.isKeyword("end"):
		logger.error("ERROR Keyword 'end' expected!")
		raise AnaSynException("Keyword 'end' expected!")
			
	lexical_analyser.acceptKeyword("end")

	#Dépiler le flag dépendance
	flagDependance.pop()
	
	lexical_analyser.acceptFel()
	generate_code("finProg()")
	logger.debug("End of program")
	
def partieDecla(lexical_analyser):
	if lexical_analyser.isKeyword("procedure") or lexical_analyser.isKeyword("function") :
		listeDeclaOp(lexical_analyser)
		if not lexical_analyser.isKeyword("begin"):
			listeDeclaVar(lexical_analyser)
	else:
		listeDeclaVar(lexical_analyser)  

def listeDeclaOp(lexical_analyser):
	declaOp(lexical_analyser)
	lexical_analyser.acceptCharacter(";")
	if lexical_analyser.isKeyword("procedure") or lexical_analyser.isKeyword("function") :
		listeDeclaOp(lexical_analyser)

def declaOp(lexical_analyser):
	if lexical_analyser.isKeyword("procedure"):
		procedure(lexical_analyser)
	if lexical_analyser.isKeyword("function"):
		fonction(lexical_analyser)

def procedure(lexical_analyser):
	global ident
	lexical_analyser.acceptKeyword("procedure")
	ident = lexical_analyser.acceptIdentifier()
	logger.debug("Name of procedure : "+ident)
	generate_code("Name" + ident)

	#Entrer le nom de la procédure dans la table des identificateurs
	identifierTable.append([ident,"NONE",flagDependance[-1],"PROCEDURE","",""])
	#Empiler le nom dans le flag dépendance
	flagDependance.append(ident)
 
	partieFormelle(lexical_analyser)
	lexical_analyser.acceptKeyword("is")
	corpsProc(lexical_analyser)
	generate_code("retourProc()")


def fonction(lexical_analyser):
	global ident
	lexical_analyser.acceptKeyword("function")
	ident = lexical_analyser.acceptIdentifier()
	logger.debug("Name of function : "+ident)
	generate_code("Name" + ident)

	#Entrer le nom de la fonction dans la table des identificateurs
	identifierTable.append([ident,"NONE",flagDependance[-1],"FONCTION","",""])
	#Empiler le nom dans le flag dépendance
	flagDependance.append(ident)

	partieFormelle(lexical_analyser)
	lexical_analyser.acceptKeyword("return")
	nnpType(lexical_analyser)
    
	lexical_analyser.acceptKeyword("is")
	corpsFonct(lexical_analyser)
	generate_code("sortieFonction")

def corpsProc(lexical_analyser):
	if not lexical_analyser.isKeyword("begin"):
		partieDeclaProc(lexical_analyser)
	lexical_analyser.acceptKeyword("begin")
	suiteInstr(lexical_analyser)
	lexical_analyser.acceptKeyword("end")

	#Dépiler le flag dépendance
	flagDependance.pop()

def corpsFonct(lexical_analyser):
	if not lexical_analyser.isKeyword("begin"):
		partieDeclaProc(lexical_analyser)
	lexical_analyser.acceptKeyword("begin")
	suiteInstrNonVide(lexical_analyser)
	lexical_analyser.acceptKeyword("end")

	#Dépiler le flag dépendance
	flagDependance.pop()

def partieFormelle(lexical_analyser):
	lexical_analyser.acceptCharacter("(")
	if not lexical_analyser.isCharacter(")"):
		listeSpecifFormelles(lexical_analyser)
	lexical_analyser.acceptCharacter(")")

def listeSpecifFormelles(lexical_analyser):
	specif(lexical_analyser)
	if not lexical_analyser.isCharacter(")"):
		lexical_analyser.acceptCharacter(";")
		listeSpecifFormelles(lexical_analyser)

def specif(lexical_analyser):
	global flagParameter

	#Armer un flag qui indique qu'on va entrer des paramètres
	flagParameter=True

	listeIdent(lexical_analyser)

	#Désarmer le flag
	flagParameter=False

	#Récupérer le nombre de paramètres
	j=1
	compteur=0
	while identifierTable[-j][CLASS]=="PARAMETER":
		compteur+=1
		j+=1	

	identifierTable[-j][PLACE]=compteur    

	lexical_analyser.acceptCharacter(":")
	if lexical_analyser.isKeyword("in"):
		mode(lexical_analyser)
                
	nnpType(lexical_analyser)

def mode(lexical_analyser):                  
	lexical_analyser.acceptKeyword("in")
	if lexical_analyser.isKeyword("out"):
		lexical_analyser.acceptKeyword("out")
		logger.debug("in out parameter")                
	else:
		logger.debug("in parameter")

def nnpType(lexical_analyser):
	if lexical_analyser.isKeyword("integer"):
		lexical_analyser.acceptKeyword("integer")

		#Récupérer le fait que le ou les identificateur(s) est ou sont de type int
		i=1
		while identifierTable[-i][TYPE]=="":
			identifierTable[-i][TYPE]="integer"
			i+=1

		logger.debug("integer type")
	elif lexical_analyser.isKeyword("boolean"):
		lexical_analyser.acceptKeyword("boolean")

		#Récupérer le fait que le ou les identifateur(s) est ou sont de type boolean
		i=1
		while identifierTable[-i][TYPE]=="":
			identifierTable[-i][TYPE]="boolean"
			i+=1
		
		logger.debug("boolean type")                
	else:
		logger.error("Unknown type found <"+ lexical_analyser.get_value() +">!")
		raise AnaSynException("Unknown type found <"+ lexical_analyser.get_value() +">!")

def partieDeclaProc(lexical_analyser):
	listeDeclaVar(lexical_analyser)

def listeDeclaVar(lexical_analyser):
	declaVar(lexical_analyser)
	if lexical_analyser.isIdentifier():
		listeDeclaVar(lexical_analyser)

def declaVar(lexical_analyser):
	listeIdent(lexical_analyser)
	lexical_analyser.acceptCharacter(":")
	logger.debug("now parsing type...")
	nnpType(lexical_analyser)
	lexical_analyser.acceptCharacter(";")
	generate_code("finDeclaVar")

def listeIdent(lexical_analyser):
	global ident
	ident = lexical_analyser.acceptIdentifier()

	#Entrer le nom de l'identificateur dans la table des identificateurs
	if flagParameter:
	
		#Récupérer l'adresse de l'identificateur
		adresse=0

		#Si l'identificateur précédent est une fonction ou une procédure, on met l'adresse à 1
		if identifierTable[-1][TYPE]=="FONCTION" or identifierTable[-1][TYPE]=="PROCEDURE":
			adresse=0
		#Si l'identificateur précédent est un paramètre, on met l'adresse à l'adresse de l'identificateur précédent +1
		elif identifierTable[-1][CLASS]=="PARAMETER":
			adresse=identifierTable[-1][ADRESSE]+1
	
		identifierTable.append([ident,"PARAMETER",flagDependance[-1],"",adresse,""])

	else:
		
		#Récupérer l'adresse de l'identificateur
		adresse=0
		#Si l'identificateur précédent est une fonction ou une procédure, on met l'adresse à 1
		if identifierTable[-1][TYPE]=="FONCTION" or identifierTable[-1][TYPE]=="PROCEDURE" or identifierTable[-1][CLASS]=="PARAMETER" or identifierTable[-1][DEPENDANCE]!=flagDependance[-1]:
			adresse=0
		#Si l'identificateur précédent est une variable locale, on met l'adresse à l'adresse de l'identificateur précédent +1
		elif identifierTable[-1][CLASS]=="LOC":
			adresse=identifierTable[-1][ADRESSE]+1

		identifierTable.append([ident,"LOC",flagDependance[-1],"",adresse,""])

	logger.debug("identifier found: "+str(ident))

	global nb_var
	nb_var += 1 # On incrémente le nombre de variables à déclarer

	if lexical_analyser.isCharacter(","):
		lexical_analyser.acceptCharacter(",")
		listeIdent(lexical_analyser)

def suiteInstrNonVide(lexical_analyser):
	instr(lexical_analyser)
	if lexical_analyser.isCharacter(";"):
		lexical_analyser.acceptCharacter(";")
		suiteInstr(lexical_analyser)

def suiteInstr(lexical_analyser):
	if not lexical_analyser.isKeyword("end"):
		suiteInstrNonVide(lexical_analyser)

def instr(lexical_analyser):		
	global ident, type_affectation, exp
	# On initialise les variables pour l'analyse de l'expression
	exp = []
	if lexical_analyser.isKeyword("while"):
		boucle(lexical_analyser)
	elif lexical_analyser.isKeyword("if"):
		altern(lexical_analyser)
	elif lexical_analyser.isKeyword("get") or lexical_analyser.isKeyword("put"):
		es(lexical_analyser)
	elif lexical_analyser.isKeyword("return"):
		retour(lexical_analyser)
	elif lexical_analyser.isIdentifier():
		ident = lexical_analyser.acceptIdentifier()
		# Vérifier si l'identificateur est une variable accessible :
		if not is_declared(ident, flagDependance[-1]):
			# Si c'est pas le cas on renvoi une erreur
			logger.error(f"Undeclared identifier used: {ident}")
			raise AnaSynException(f"Undeclared identifier used: {ident}")
		if lexical_analyser.isSymbol(":="):
			# récuperer le type de l'identificateur auquel on veut affecter une valeur :
			type_affectation = get_type(ident, flagDependance[-1])
            # affectation
			lexical_analyser.acceptSymbol(":=")
			generate_code("appelVar" + ident)
			affected_type = expression(lexical_analyser) # On récupère le type
			# On vérifie que le type affecté est bon
			check_type(type_affectation, affected_type, "affectation") 
			generate_code("affectation()")
			logger.debug("parsed affectation")
		elif lexical_analyser.isCharacter("("):
			lexical_analyser.acceptCharacter("(")
			function = ident # l'identificateur est une fonction ou une procédure donc on le met de coté
			if not lexical_analyser.isCharacter(")"):
				# s'il y a des paramètre on ajoute un element à params, initialisé à 1 car il y en a au moins 1
				params.append(1)
				listePe(lexical_analyser)
			else : 
				# s'il n'y en a pas, initialisé à 0
				params.append(0)
			generate_code("appelProcFonc" + function)
			lexical_analyser.acceptCharacter(")")
			logger.debug("parsed procedure call")
			# On vérifie que la fonction appelée est définie et que le nombre de paramètres est bon
			check_function_call(function, params, flagDependance[-1])
			# on supprime le dernier element de param car est inutile et cela permet l'appel d'une fonction dans l'appel d'une autre
			if params != [] :
				params.pop()
			logger.debug("Call to function: " + function)
		else:
			logger.error("Expecting procedure call or affectation!")
			raise AnaSynException("Expecting procedure call or affectation!")
		
	else:
		logger.error("Unknown Instruction <"+ lexical_analyser.get_value() +">!")
		raise AnaSynException("Unknown Instruction <"+ lexical_analyser.get_value() +">!")


# Fonction renvoyant la liste des paramêtre de la fonction/procédure en cours d'analyse
def listePe(lexical_analyser):
	global params, exp, lstVariablesAppelees
	expression(lexical_analyser)
	lstVariablesAppelees += [exp.copy()] 
	if lexical_analyser.isCharacter(","):
		lexical_analyser.acceptCharacter(",")
		params[-1] += 1 # on incrémente le compteur de paramètres
		listePe(lexical_analyser)

def expression(lexical_analyser):
	logger.debug("parsing expression: " + str(lexical_analyser.get_value()))
	global left_type , exp
	left_type = exp1(lexical_analyser) # On récupère le "type à gauche"
	# Si nous somme dans une expression, il y a un type à gauche qui doit toujours coïncider avec le type à droite
	if lexical_analyser.isKeyword("or"):
		lexical_analyser.acceptKeyword("or")
		exp.append("ou()")
		right_type = exp1(lexical_analyser) # On récupère le type à droite
		# Comme on est dans un or, on vérifie que les types à gauche et à droite du or sont des booléens
		check_type("boolean", left_type, "or")
		check_type("boolean", right_type, "or")
		left_type = "boolean" 
	return left_type # On retourne le type à gauche (booléen si on était dans une instruction or)

def exp1(lexical_analyser):
	global left_type, exp
	logger.debug("parsing exp1")
	left_type = exp2(lexical_analyser) # On récupère le "type à gauche"
	# Si nous somme dans une expression, il y a un type à gauche qui doit toujours coïncider avec le type à droite
	if lexical_analyser.isKeyword("and"):
		lexical_analyser.acceptKeyword("and")
		exp.append("et()")
		right_type = exp2(lexical_analyser) # On récupère le type à droite
		# Comme on est dans un and, on vérifie que les types à gauche et à droite du or sont des booléens
		check_type("boolean", left_type, "and")
		check_type("boolean", right_type, "and")
		left_type = "boolean"
	return left_type # On retourne le type à gauche (booléen si on était dans une instruction and)
    
def exp2(lexical_analyser):
	global left_type     
	logger.debug("parsing exp2")
	left_type = exp3(lexical_analyser) # On récupère le "type à gauche"
	# Si nous somme dans une comparaison, il y a un type à gauche qui doit toujours coïncider avec le type à droite (integer)
	if	lexical_analyser.isSymbol("<") or \
		lexical_analyser.isSymbol("<=") or \
		lexical_analyser.isSymbol(">") or \
		lexical_analyser.isSymbol(">="):
		opRel(lexical_analyser)
		right_type = exp3(lexical_analyser) # On récupère le type à droite
		# On vérifie que les types de chaque coté de la comparaison sont des entiers
		check_type("integer", right_type, "comparison")
		check_type("integer", left_type, "comparison")
		left_type = "boolean"
	elif lexical_analyser.isSymbol("=") or \
		lexical_analyser.isSymbol("/="): 
		opRel(lexical_analyser)
		right_type = exp3(lexical_analyser) # On récupère le type à droite
		# On vérifie que les types de chaque coté de la comparaison sont les mêmes
		check_type(left_type, right_type, "comparison") 
		left_type = "boolean"
	return left_type # On retourne le type à gauche (booléen si on était dans une instruction comparaison)

def opRel(lexical_analyser):
	global exp
	logger.debug("parsing relationnal operator: " + lexical_analyser.get_value())
        
	if	lexical_analyser.isSymbol("<"):
		lexical_analyser.acceptSymbol("<")
		exp.append("inf()")

        
	elif lexical_analyser.isSymbol("<="):
		lexical_analyser.acceptSymbol("<=")
		exp.append("infeg()")

        
	elif lexical_analyser.isSymbol(">"):
		lexical_analyser.acceptSymbol(">")
		exp.append("sup()")

        
	elif lexical_analyser.isSymbol(">="):
		lexical_analyser.acceptSymbol(">=")
		exp.append("supeg()")

        
	elif lexical_analyser.isSymbol("="):
		lexical_analyser.acceptSymbol("=")
		exp.append("egal()")

        
	elif lexical_analyser.isSymbol("/="):
		lexical_analyser.acceptSymbol("/=")
		exp.append("diff()")

        
	else:
		msg = "Unknown relationnal operator <"+ lexical_analyser.get_value() +">!"
		logger.error(msg)
		raise AnaSynException(msg)
	
def exp3(lexical_analyser):
	global left_type
	logger.debug("parsing exp3")
	left_type = exp4(lexical_analyser) # On récupère le "type à gauche"
	# Si nous somme dans une opération, il y a un type à gauche qui doit toujours coïncider avec le type à droite (integer)
	if lexical_analyser.isCharacter('+') or lexical_analyser.isCharacter('-'):
		opAdd(lexical_analyser)
		right_type = exp4(lexical_analyser) # On récupère le type à droite
		# On vérifie que les types de chaque coté de la comparaison sont des integer
		check_type("integer", left_type, "addition/subtraction")
		check_type("integer", right_type, "addition/subtraction")
		left_type = "integer"
	return left_type # On retourne le type à gauche (integer si soustraction ou addition)

def opAdd(lexical_analyser):
	global exp
	logger.debug("parsing additive operator: " + lexical_analyser.get_value())
	if lexical_analyser.isCharacter("+"):
		lexical_analyser.acceptCharacter("+")
		exp.append("add()")

                
	elif lexical_analyser.isCharacter("-"):
		lexical_analyser.acceptCharacter("-")
		exp.append("sous()")

                
	else:
		msg = "Unknown additive operator <"+ lexical_analyser.get_value() +">!"
		logger.error(msg)
		raise AnaSynException(msg)

def exp4(lexical_analyser):
	logger.debug("parsing exp4")
	global left_type 
	left_type = prim(lexical_analyser) # On récupère le "type à gauche"
	# Si nous somme dans une opération, il y a un type à gauche qui doit toujours coïncider avec le type à droite (integer)
	if lexical_analyser.isCharacter('*') or lexical_analyser.isCharacter('/'):
		opMult(lexical_analyser)
		right_type = prim(lexical_analyser) # On récupère le type à droite
		# On vérifie que les types de chaque coté de la comparaison sont des integer
		check_type("integer", left_type, "multiplication/division")
		check_type("integer", right_type, "multiplication/division")
		left_type = "integer"
	return left_type # On retourne le type à gauche (integer si multiplication ou division)

def opMult(lexical_analyser):
	global exp
	logger.debug("parsing multiplicative operator: " + lexical_analyser.get_value())
	if lexical_analyser.isCharacter("*"):
		lexical_analyser.acceptCharacter("*")
		exp.append("mult()")

                
	elif lexical_analyser.isCharacter("/"):
		lexical_analyser.acceptCharacter("/")
		exp.append("div()")

                
	else:
		msg = "Unknown multiplicative operator <"+ lexical_analyser.get_value() +">!"
		logger.error(msg)
		raise AnaSynException(msg)

def prim(lexical_analyser):
	logger.debug("parsing prim")
        
	if lexical_analyser.isCharacter("+") or lexical_analyser.isCharacter("-") or lexical_analyser.isKeyword("not"):
		opUnaire(lexical_analyser)
	return elemPrim(lexical_analyser)

def opUnaire(lexical_analyser):
	global exp
	logger.debug("parsing unary operator: " + lexical_analyser.get_value())
	if lexical_analyser.isCharacter("+"):
		lexical_analyser.acceptCharacter("+")
                
	elif lexical_analyser.isCharacter("-"):
		lexical_analyser.acceptCharacter("-")
		exp.append("moins()")

                
	elif lexical_analyser.isKeyword("not"):
		lexical_analyser.acceptKeyword("not")
		exp.append("non()")

                
	else:
		msg = "Unknown additive operator <"+ lexical_analyser.get_value() +">!"
		logger.error(msg)
		raise AnaSynException(msg)

def elemPrim(lexical_analyser):
	global left_type, ident, params, exp, lstVariablesAppelees
	logger.debug("parsing elemPrim: " + str(lexical_analyser.get_value()))
	if lexical_analyser.isCharacter("("):
		lexical_analyser.acceptCharacter("(")
		exp.append("(")
		left_type = expression(lexical_analyser) # On récupère le "type à gauche"
		# On rentre dans une parenthèse comprenant une opération ou un identifiant
		lexical_analyser.acceptCharacter(")")
		exp.append(")")
		return left_type # On renvoit le type qu'on obtient
	elif lexical_analyser.isInteger() or lexical_analyser.isKeyword("true") or lexical_analyser.isKeyword("false"):
		return valeur(lexical_analyser) # renvoi le type integer ou boolean selon si il s'agit de l'un ou de l'autre
	elif lexical_analyser.isIdentifier():
		#Vérifie si l'identificateur est une variable accessible :
		ident = lexical_analyser.acceptIdentifier() # On récupère l'identificateur
		# On vérifie si il est déclaré (présent dans la table)
		if not is_declared(ident, flagDependance[-1]):
			# Si ce n'est pas le cas on lève une erreur
			logger.error(f"Undeclared identifier used: {ident}")
			raise AnaSynException(f"Undeclared identifier used: {ident}")
		
		if lexical_analyser.isCharacter("("):			# Appel fonct
			lexical_analyser.acceptCharacter("(")
			function = ident # l'identificateur est une fonction ou une procédure donc on le met de coté
			if not lexical_analyser.isCharacter(")"):
				# Si la parenthèse n'est pas refermée directement, c'est qu'il y a des paramêtres
				params.append(1) # on ajoute un element à params, initialisé à 1 (au moins 1 param)
				listePe(lexical_analyser)
			else : 
				# s'il n'y a pas de paramètres, on ajoute un élément à params initialisé à 0
				params.append(0)
			lexical_analyser.acceptCharacter(")")
			generate_code("appelProcFonc" + function)
			logger.debug("parsed procedure call")
			# On vérifie que la fonction (ou procédure) à laquelle on fait appel existe
			# Et qu'il y a le bon nombre de paramètres
			check_function_call(function, params, flagDependance[-1])
			# On supprime le dernière élément de params pour permettre l'appel imbriqué de fonction
			if params != [] : 
				params.pop()
			logger.debug("Call to function: " + function)
		else:
			logger.debug("Use of an identifier as an expression: " + ident)
			exp.append(ident) # ajout du terme dans la sous-expression
		return get_type(ident, flagDependance[-1]) # On retourne le type de l'identificateur si il ne s'agit ni d'une fonction ni d'une procédure
	else:
		logger.error("Unknown Value!")
		raise AnaSynException("Unknown Value!")


def valeur(lexical_analyser):
	global exp
	if lexical_analyser.isInteger():
		entier = lexical_analyser.acceptInteger()
		# ajout du terme dans la sous-expression
		exp.append(entier)
		logger.debug("integer value: " + str(entier))
		return "integer"
	elif lexical_analyser.isKeyword("true") or lexical_analyser.isKeyword("false"):
		vtype = valBool(lexical_analyser)
		return vtype
	else:
		logger.error("Unknown Value! Expecting an integer or a boolean value!")
		raise AnaSynException("Unknown Value ! Expecting an integer or a boolean value!")

def valBool(lexical_analyser):
	global exp
	if lexical_analyser.isKeyword("true"):
		lexical_analyser.acceptKeyword("true")	
		logger.debug("boolean true value")
		# ajout du terme dans la sous-expression
		exp.append(True)
                
	else:
		logger.debug("boolean false value")
		lexical_analyser.acceptKeyword("false")
		exp.append(False)	
        
	return "boolean"

def es(lexical_analyser):
	global ident
	logger.debug("parsing E/S instruction: " + lexical_analyser.get_value())
	if lexical_analyser.isKeyword("get"):
		lexical_analyser.acceptKeyword("get")
		lexical_analyser.acceptCharacter("(")
		ident = lexical_analyser.acceptIdentifier() # On récupère l'identificateur à l'intérieur du get
		lexical_analyser.acceptCharacter(")")
		generate_code("get" + ident)
		logger.debug("Call to get "+ident)
		# On vérifie si il est déclaré 
		if not is_declared(ident, flagDependance[-1]):
			# Si ce n'est pas le cas on lève une erreur
			logger.error(f"Undeclared identifier used: {ident}")
			raise AnaSynException(f"Undeclared identifier used: {ident}")
		# On récupère son type dans la table des identificateur et on vérifie que ce n'est pas un boolean
		if get_type(ident, flagDependance[-1])=="boolean":
			# Si c'est le cas on lève une erreur
			logger.error(f"Boolean not allowed in get instruction : {ident}")
			raise AnaSynException(f"Boolean not allowed in get instruction : {ident}")
	elif lexical_analyser.isKeyword("put"):
		lexical_analyser.acceptKeyword("put")
		lexical_analyser.acceptCharacter("(")
		global exp
		expr_type = expression(lexical_analyser) # On récupère le type de l'expression à l'interieur du put
		if expr_type=="boolean":
			# On lève une erreur si l'expresson est booléenne
			logger.error(f"Boolean not allowed in put instruction : {ident}")
			raise AnaSynException(f"Boolean not allowed in put instruction : {ident}")
		generate_code("put")
		lexical_analyser.acceptCharacter(")")
        # Pas de vérification de type spécifique nécessaire ici
		logger.debug("Call to put")
	else:
		logger.error("Unknown E/S instruction!")
		raise AnaSynException("Unknown E/S instruction!")
	logger.debug("parsed I/O statement")

def boucle(lexical_analyser):
	global exp
	logger.debug("parsing while loop: ")
	lexical_analyser.acceptKeyword("while")
	expr_type = expression(lexical_analyser) # On récupère le type de l'expression du while
	generate_code("tze")
	# On vérifie que c'est un boolean
	check_type("boolean", expr_type, "while condition")
	lexical_analyser.acceptKeyword("loop")
	suiteInstr(lexical_analyser)
	lexical_analyser.acceptKeyword("end")
	generate_code("endtzewhile")
	logger.debug("parsed while loop")

def altern(lexical_analyser):
	global exp, flagIF, nb_tze
	logger.debug("parsing if: ")
	lexical_analyser.acceptKeyword("if")
	expr_type = expression(lexical_analyser) # On récupère le type de l'expression du if
	# On vérifie que c'est un boolean
	check_type("boolean", expr_type, "if condition")
	flagIF.append(["tze" + str(nb_tze), False]) # On ajoute un flag pour savoir si le if possède un else
	generate_code("tze")
	lexical_analyser.acceptKeyword("then")
	suiteInstr(lexical_analyser)
	if lexical_analyser.isCharacter(";"):
		lexical_analyser.acceptCharacter(";")
		suiteInstr(lexical_analyser)

	if lexical_analyser.isKeyword("else"):
		lexical_analyser.acceptKeyword("else")
		generate_code("endtzeifelse")
		suiteInstr(lexical_analyser)
		if lexical_analyser.isCharacter(";"):
			# lexical_analyser.acceptCharacter(";")
			suiteInstr(lexical_analyser)
	logger.debug("parsed if statement")
	lexical_analyser.acceptKeyword("end")
	generate_code("endtzeifend")
	generate_code("tra")
	logger.debug("end of if")

# VOIR POUR AJOUTER UNE COLONE DE TYPE DE RETOUR DANS LA TABLE DES IDENTIFICATEURS
#  puis faire la fonction get_funtion_return_type
def retour(lexical_analyser):
	logger.debug("parsing return instruction")
	lexical_analyser.acceptKeyword("return")
	expr_type = expression(lexical_analyser)
    # On récupere le type qu'est sensé retourner la fonction
	# expected_type = get_function_return_type(flagDependance[-1])
	# check_type(expected_type, expr_type, "return statement")
	logger.debug("parsed return statement")
	generate_code("retourFonct()")



############################################################################################################################################################################
### Table des identificateurs
############################################################################################################################################################################
	
# Cette fonction renvoie l'adresse de localisation d'un identificateur à l'aide de la table des identificateurs
def adresse(identificateur,dependance):
	for i in range(len(identifierTable)):
		if identifierTable[i][NOM]==identificateur and identifierTable[i][DEPENDANCE]==dependance:
			return identifierTable[i][ADRESSE]


# Si l'identificateur est une variable, on renvoie True, sinon on renvoie False (il s'agit d'une variable)
def is_param(identificateur, dependance):
    for i in range(len(identifierTable)):
        if identifierTable[i][NOM]==identificateur and identifierTable[i][DEPENDANCE]==dependance and identifierTable[i][CLASS]=="PARAMETER":
            return True
    return False

########################################################################				 	
def main():
 	
	parser = argparse.ArgumentParser(description='Do the syntactical analysis of a NNP program.')
	parser.add_argument('inputfile', type=str, nargs=1, help='name of the input source file')
	parser.add_argument('-o', '--outputfile', dest='outputfile', action='store', \
                default="", help='name of the output file (default: stdout)')
	parser.add_argument('-v', '--version', action='version', version='%(prog)s 1.0')
	parser.add_argument('-d', '--debug', action='store_const', const=logging.DEBUG, \
                default=logging.INFO, help='show debugging info on output')
	parser.add_argument('-p', '--pseudo-code', action='store_const', const=True, default=False, \
                help='enables output of pseudo-code instead of assembly code')
	parser.add_argument('--show-ident-table', action='store_true', \
                help='shows the final identifiers table')
	args = parser.parse_args()

	filename = args.inputfile[0]
	f = None
	try:
		f = open(filename, 'r')
	except:
		print("Error: can\'t open input file!")
		return
		
	outputFilename = args.outputfile
	
  	# create logger      
	LOGGING_LEVEL = args.debug
	logger.setLevel(LOGGING_LEVEL)
	ch = logging.StreamHandler()
	ch.setLevel(LOGGING_LEVEL)
	formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
	ch.setFormatter(formatter)
	logger.addHandler(ch)

	if args.pseudo_code:
		True#
	else:
		False#

	lexical_analyser = analex.LexicalAnalyser()
	
	lineIndex = 0
	for line in f:
		line = line.rstrip('\r\n')
		lexical_analyser.analyse_line(lineIndex, line)
		lineIndex = lineIndex + 1
	f.close()

	# launch the analysis of the program
	lexical_analyser.init_analyser()
	program(lexical_analyser)
		
	if args.show_ident_table:
			print("------ IDENTIFIER TABLE ------")
			print(str(identifierTable))
			print("------ END OF IDENTIFIER TABLE ------")


	if outputFilename != "":
			try:
					output_file = open(outputFilename, 'w')
			except:
					print("Error: can\'t open output file!")
					return
	else:
			output_file = sys.stdout

	# Outputs the generated code to a file
	#instrIndex = 0
	#while instrIndex < codeGenerator.get_instruction_counter():
	#	output_file.write("%s\n" % str(codeGenerator.get_instruction_at_index(instrIndex)))
	#	instrIndex += 1

		
	if outputFilename != "":
			output_file.close() 
	
	# On génère ici des fichiers .txt du code généré
	global codeGenerator
	dir = "./tests/code_genere/"
	sous_nom = filename.split("/")
	nom = "genere" + sous_nom[2] + "" + sous_nom[3].split(".")[0]
	with open(dir + nom + ".txt", "w") as f:
		for instruction in codeGenerator:
			f.write(instruction + "\n")
########################################################################				 

if __name__ == "__main__":
    main() 
