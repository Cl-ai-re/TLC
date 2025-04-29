import argparse

def number(line,j):
    a=line[j+1]
    s=0
    nb=[]
    i=j+1
    while a!=")" and a!=",":
        i+=1
        nb.append(int(a))
        a=line[i]
    nb_size=len(nb)
    for i in range(nb_size):
        s+=10**(nb_size-i-1) * nb[i]
    return (s,j+nb_size+1)

def identification(line):
    char=line[0]
    txt=""
    i=0
    while char!="(":
        i+=1
        txt+=char
        char=line[i]
    return (txt,i)

def tableau(f) :
    table=[]
    txt = f.readline()
    while(txt != '') :
        table.append(txt)
        txt = f.readline()
    return table

def tout(code,pile):
   
    i=0
    base=[0]
    while i!=len(code)-1:
        i+=1
        f=code[i-1]
        (txt,j)=identification(f)
        match txt:
            case "debutProg":
                pile=[]

            case "finProg":
                return True

            case "affectation":
                pile[pile[-2]]=pile[-1]

            case "valeurPile":
                pile[-1]=pile[pile[-1]]


            case "get":
                print('entrer une valeur :')
                val = int(input())
                pile[pile[-1]]=val
                pile.pop()
            
            case "put":
                print(pile.pop())
            
            case "moins":
                pile[-1] = -pile[-1]
            case "sous":
                x = pile.pop()
                pile[-1] -= x
            case "add":
                x = pile.pop()
                pile[-1] += x
            case "mult":
                x = pile.pop()
                pile[-1] *= x
            case "div":
                x = pile.pop()
                pile[-1] //= x
            case "egal":
                x = pile.pop()
                if(pile[-1] == x) :
                    pile[-1] = True
                else :
                    pile[-1] = False      
            case "diff":
                x = pile.pop()
                if(pile[-1] != x) :
                    pile[-1] = True
                else :
                    pile[-1] = False
            case "inf":
                x = pile.pop()
                if(pile[-1] < x) :
                    pile[-1] = True
                else :
                    pile[-1] = False
            case "infeg":
                 x = pile.pop()
                 if(pile[-1] <= x) :
                    pile[-1] = True
                 else :
                    pile[-1] = False       
            case "sup":
                x = pile.pop()
                if(pile[-1] > x) :
                    pile[-1] = True
                else :
                    pile[-1] = False 
            case "supeg":
                x = pile.pop()
                if(pile[-1] >= x) :
                    pile[-1] = True
                else :
                    pile[-1] = False
            case "et":
                x = pile.pop()
                if(pile[-1] and x) :
                    pile[-1] = True
                else :
                    pile[-1] = False
            case "ou":
                x = pile.pop()
                if(pile[-1] or x) :
                    pile[-1] = True
                else :
                    pile[-1] = False
            case "non":
                pile[-1] = not pile[-1]
            
            case "reserverBloc":
                pile.append(base[-1])
                pile.append('')
            
            case "traStat":
                (a,k)=number(f,j)
                (nbp,k)=number(f,k)
                pile[-nbp-1]=i+1
                i=a-1
                base.append(len(pile)-nbp)            
            case "retourFonct":
                while len(pile)!=base[-1]+1:
                    pile.pop(-2)
                i=pile.pop(-2)-1
                pile.pop(-2)
                base.pop()
            
            case "retourProc":
                while len(pile)!=base[-1]:
                    pile.pop()
                i=pile.pop()-1
                pile.pop()
                base.pop()

            case "empilerParam":
                nb=number(f,j)[0]
                pile.append(pile[base[-1]+nb+1])

            case "reserver":
                nb=number(f,j)[0]
                for _ in range(nb):
                    pile.append('')
                    

            case "empiler":
                nb=number(f,j)[0]
                pile.append(nb)

            case "empilerAd":
                nb=number(f,j)[0]
                pile.append(nb+base[-1])

            case "tra":
                nb=number(f,j)[0]
                i=nb-1

            case "tze":
                nb=number(f,j)[0]
                if (pile.pop()==0):
                    i=nb-1

            case "erreur":
                nb=number(f,j)
        

def compilateur(f) :
    code = tableau(f)
    pile =[]
    tout(code,pile)




def main() :
    parser = argparse.ArgumentParser(description='Execute le code objet')
    parser.add_argument('inputfile', type=str, nargs=1, help='name of the input source file')
    args = parser.parse_args()
    filename = args.inputfile[0]
    f = None
    try:
        f = open("./fourniture/fourniture/tests/code_genere/" + filename, 'r')
    except:
        print("Error: can\'t open input file!",".fourniture/fourniture/tests/code_genere/" + filename)
        return
    print("execution de" + filename)
    compilateur(f)
    print("execution fini")    

########################################################################				 

if __name__ == "__main__":
    main() 

    
