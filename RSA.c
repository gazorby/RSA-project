#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include <string.h>
#include <stdint-gcc.h>

// test si le nombre est un multiple d'un des 3 premiers nombres premiers (3, 5, 7)
int Multiple (unsigned long long a)
{
    unsigned long long i=1,j=3;

    while(i!=0 && a!=j && j<19)
    {
        if(j==9 || j==15)
            j+=2;

        i = fmod(a,j);
        j+= 2;
    }

    if (j==19 || a==j)
        return 0;

    else
        return 1;
}

// renvoi un nombre aléatoire impair égal à (2*a*b*c)-1, avec a,b et c compris entre 5 et 60.
unsigned long long Aleatoire()
{
    unsigned long long resultat,a,b;

    srand( time(NULL)*rand()%99999 ); // initialisation de rand par le produit nombre pseudo-aléatoire compris entre 0 et 99999, et le nombre de secondes écoulées depuis 1970
    a = rand()%(60-5) + 5;

    srand( time(NULL)*a*rand()); // réinitialisation de rand, avec rajout du facteur "a"
    b = rand()%(60-5) + 5;

    resultat = (2 * a * b) - 1; // on multiplie par 2 puis on soustrait 1 pour avoir un nombre impair
    return resultat;
}

// Génère un nombre premier à partir d'un nombre aléatoire de la fonction "Aleatoire"
unsigned long long Generateur_Premier ()
{
    unsigned long long nombre,i,divisible,racine;
    int premier;

    premier = 0;
    nombre = Aleatoire();

    while(premier == 0)
    {
        i = 1;
        divisible = 0;

        racine = round(sqrt(nombre));  // calcul de la valeur approchée de la racine carrée de "nombre"

        // si le nombre est un multiple d'un nombre premier, et différent de 2,
        // alors le nombre n'est pas prmeier
        while(Multiple(nombre)==1)
            nombre+= 2;


        // Sinon on test si "nombre" est divisble par tout les nombre inférieurs à "racine",
        // exepté les nombre multiples des nombres premiers 3,5,7,11,13,17 et 19
        while (i<racine && divisible==0)
        {
            i+=2;

            if( Multiple(i)==0 && fmod(nombre,i)==0 )
                divisible = 1;
        }

        if ((i==racine || nombre==2) && nombre!=1)
            premier = 1;

        else
            nombre+= 2;
    }
    return nombre;
}

// renvoi le PGCD de deux nombres
unsigned long long PGCD (int a, int b)
{
    int reste;

    while(fmod(a,b)!=0)
    {
        reste = fmod(a,b);
        a = b;
        b = reste;
    }
    return b;
}

// renvoi "u", faisant partie du couple de solutions (u,v) de l'équation diophantienne au + bv = c
// Selon l'identité de Bezout ax + by = pgcd(a,b). Ici, c sera donc toujours égal à 1, car a et b sont premier entre eux.
uint64_t Euclide_etendu (uint64_t a, uint64_t b)
{
    unsigned long long r = a, u = 1, v = 0;
    unsigned long long rx = b, ux = 0, vx = 1, q;
    unsigned long long rs, us, vs;  // variables intermédiares

    while(rx != 0)
    {
        q = r/rx;
        rs = r;
        us = u;
        vs = v;
        r = rx;
        u = ux;
        v = vx;
        rx = rs - (q*rx);
        ux = us - (q*ux);
        vx = vs - (q*vx);
    }

    return u;
}


uint64_t Expo_Modulaire (uint64_t base, uint64_t exp, uint64_t mod)
{
    uint64_t r = 1;
    int i;

    if(mod == 1)
        return 0;

    for(i=1; i<=exp; i++)
        r = (r*base)%mod;

    return r;
}


void Vider_Buffer_Clavier ()
{
    int a;

    do {
        a = getchar();
    } while (a != '\n' && a != EOF);
}


int main(int argc, char **argv)
{
    uint64_t p, q, n, phi_n, e, d; // variables nécessaires aux calculs des clés de cryptage
    int i, taille;
    char recommencer = 0;
    clock_t t1, t2, t3, t4, t5, t6; // type permettant de stocker le temps processeur
    long clock_tik = CLOCKS_PER_SEC; // nombre d'unités de temps processeur par secondes (tick par secondes)

    do
    {
        t1 = clock(); // renvoi le temps de l'horloge du processeur


        /// Génération des clés ///


        p = Generateur_Premier();
        q = Generateur_Premier();

        printf("p %I64u \n\n", p);
        printf("q %I64u \n\n", q);

        n = p*q;
        printf("n %I64u \n\n", n);

        phi_n = (p-1) * (q-1);
        printf("phi_n %I64u \n\n", phi_n);

        if( (q - p) < 0 ) // le plus grand nombre de p ou de q est affecté à e
            e = p;

        else
            e = q;

        srand( time(NULL)%p + n);
        e = rand()%(phi_n-e-1) + e;


        while(PGCD(phi_n,e) != 1)   e++; // on cherche e tel que :  e < phi_n  et PGCD(phi_n,e)=1

        printf("e %I64u \n\n",e);


        /*
          On sait que d est un nombre tel que e*d est congru à 1 mod(phi_n).
          d est l'inverse modulaire de e mod(phi_n), on peut donc écrire :

          e*d + k*phi_n = 1   ou k est un entier relatif.

          On ne cherche qu'a déterminer d.

          On a alors une équation diophantienne de type ax + by = c qui peut être résolue en utilisant
          l'algorithme d'euclide étendu.

          Cependant, selon le cryptage RSA :   p,q < d < phi_n
          Et il se peut (et c'est souvent le cas) que l'algorithme d'euclide étendu ne donne pas une valeur
          de d comprise dans l'intervalle.

          Soit aX + bY = c une solution connue de ax + by = c, avec a et b premiers entre eux (PGCD(a,b)=1).
          par soustraction membre à membre, on a : a(x-X) + b(y-Y) = 0
          Or, a et b sont premiers entre eux, et x,X,y et Y sont des entier relatifs. Donc :

          a divise (y-Y) <=> y-Y = ka <=> y = Y + ka
          -b divise (x-X) <=> x-X = -kb <=> x = X - kb

          Ici, x et X valent d et b vaut phi_n. Seules les solutions de x nous intéresse
          On peut donc facilement trouver une autre valeur de d en faisant varier k.
        */

        d = Euclide_etendu(e,phi_n);

        while(d<2 || d>phi_n)
            d = d-(-1*phi_n);

        t2 = clock();

        printf("d %I64u \n\n\n",d);

        printf("Cle publique : (%I64u , %I64u) \n\n", e,n);
        printf("Cle prive : (%I64u , %I64u) \n\n\n\n", d,n);





        printf("Nombre de caracteres maximal du message : ");
        scanf("%d", &taille);
        uint64_t asci[taille];
        char message[taille];

        for(i=0; i<taille; i++)  // initialisation à 0 des tableaux qui contiendront le code ascii des caractères du message, et le message chiffré
        {
            message[i] = 0;
            asci[i] = 0;
        }

        Vider_Buffer_Clavier(); // On vide le buffer du clavier


        printf("\n\nVotre nmessage : \n\n");
        fgets(message, taille, stdin); // saisie du message


        t3 = clock();

        i = 0;

        printf("\n **********");
        printf("\n Code ASCII\n");
        printf(" **********\n\n");

        while(message[i] != 0)
        {
            printf(" - %d", message[i]);
            i++;
        }


        /// cryptage ///


        i = 0;

        while(message[i] != 0)
        {
            asci[i] = message[i];
            asci[i] = Expo_Modulaire(asci[i],e,n);
            i++;
        }

        printf("\n\n ***************");
        printf("\n Message chiffre\n");
        printf(" ***************\n\n");

        i = 0;

        while(asci[i] != 0)
        {
            printf(" - %I64u", asci[i]);
            i++;
        }

        t4 = clock();
        printf("\n\n\nAppuyer sur entree pour dechiffrer");
        getchar();



        /// décryptage ///

        t5 = clock();

        i = 0;

        while(asci[i] != 0)
        {
            asci[i] = Expo_Modulaire(asci[i],d,n);
            message[i] = asci[i];
            i++;
        }
        printf("\n\n *****************");
        printf("\n Message dechiffre\n");
        printf(" *****************\n\n");

        i = 0;

        while(asci[i] != 0)
        {
            printf(" - %I64u", asci[i]);
            i++;
        }

        printf("\n\nmessage : %s \n\n", message);

        t6 = clock();

        printf("Temps de calcul des cles : %E s \n", (double)(t2-t1)/clock_tik);
        printf("Temps de chiffrement :     %E s\n", (double)(t4-t3)/clock_tik);
        printf("Temps de dechiffrement :   %E s\n\n\n\n", (double)(t6-t5)/clock_tik);

        printf("Voulez-vous chiffrer un autre message ? (o/n) ");

        fgets(&recommencer, 2, stdin);

        Vider_Buffer_Clavier(); // On vide le buffer du clavier
    }
    while(recommencer == 'o');

    return(0);
}

