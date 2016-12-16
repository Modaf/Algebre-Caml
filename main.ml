(*Programme qui démontre des trucs sur les groupes ^^*)

(*Notations :
	-appartenance : &
	-pour tout : V
	-il existe : E
	-element neutre : e
	-intersection : n
	-union : U*)

(*Propriétés necessaire pour un groupe :
	-associativité : (a*b)*c = a*(b*c)
	-element neutre : Vx, x*e=e*x=x
	-inverse : Vx, Ey, x*y=y*x=e*)

(*Propriétés qu'on peut avoir :
	-commutativité : Vx, Vy, x*y=y*x=e*)

(*H est un sous groupe ssi stabiliter et inverse*)

(*A mq par le programme :
	-intersection de sous groupe est un sous groupe         --> DONE :D
	-sous groupe de Z = nZ											  --> DONE :D
	-image et noyau de morphismes sont des sous groupes	  --> noyau&im pour la stab : DONE :D
	-tout groupe monogene est isomorphe à Z ou Z/nZ			  --> 
	-sous groupe de groupe monogène est monogène				  --> DONE :D
	-théorème de Lagrange											  --> 
	-théorème de Cauchy :D*)

(*On veut mq sous groupe monogène est monogène :
	-ie Ex&H, Vy&H y&<x>
	-mais Ex&G, Vy&G, Ek, y=x^k
	-on prends un x dans H, <x> est dans H
	-si Ey qui n'est pas dans <x>, alors y=o^kd et x=o^md
	-donc z=o^d est dans H car Eu, Ev tq ku+mv=1 donc z=y^u * x^v et <x>, <y> inclus dans <z>
	-et ainsi de suite, H est monogène*)

(*On veut mq sous groupe de Z sont les nZ :
	-si n&H, <n> inclus dans H
	-si Ey&H tq y pas dans <n> then pgcd dans H tq <pgcd> genere les deux
	-par recurrence descendante finie, H = nZ*)

(*On veut mq le cardinal de sous groupe divise celui du groupe :
	-xRy ssi xy^-1&H (partage en classe d'<=>)
	-*)

(*Th que le prog "sait" montrer :
	-intersection de sous groupe = sous groupe
	-sous groupe d'un groupe abélien est abélien
	-sous groupe d'un groupe monogène est monogène
	-les sous groupes de Z sont les nZ
	-le noyau d'un morphisme est stable*);;





type annonyme = {nom : int; mutable appartenance : string list};; (*à changer un jour*)

let nompossibles = [|"x" ; "y"; "z"; "a"; "b"; "c"; "d"; "e"; "f"|];;

type expression =
	Et of expression*expression|
	Eg of expression list|
	Eq of expression list|
	Im of expression list|
	Ap of expression*expression|
	Op of expression*expression|
	El of string*(expression list)|
	In of string*(expression list)|
	Nn of annonyme|
	Ex of expression*expression|
	Intersection of expression list|
	Union of expression list|
	To of expression*expression|
	Mo of expression|
	Bl of string|
	expression of expression;;
	
let prefix &! a b = Et (a, b);;

let rec ecrit expr = match expr with
	|(Et (a, b)) -> ecrit a ^ " et " ^ ecrit b
	|(Eg liste) -> let rec aux l = match l with
							|[] -> ""
							|[h] -> ecrit h
							|h::q -> ecrit h ^ " = " ^ aux q
						in aux liste
	|(Eq liste) -> let rec aux l = match l with
							|[] -> ""
							|[h] -> ecrit h
							|h::q -> ecrit h ^ " <=> " ^ aux q
						in aux liste
	|(Im liste) -> let rec aux l = match l with
							|[] -> ""
							|[h] -> ecrit h
							|h::q -> ecrit h ^ " implique trivialement " ^ aux q
						in aux liste
	|(Ap (x, G)) -> ecrit x ^ "&" ^ ecrit G ^ " "
	|(Op (a, b)) -> "(" ^ ecrit a ^ "*" ^ ecrit b ^ ")"
	|(El x) -> fst x
	|(In x) -> "(" ^ fst x ^ ")^-1"
	|(Nn a) -> nompossibles.(a.nom)
	|(Ex (a, b)) -> "E" ^ ecrit a ^ "tq " ^ ecrit b
	|(Intersection liste) -> let rec aux l = match l with
										|[] -> ""
										|[h] -> ecrit h
										|h::q -> ecrit h ^ "n" ^ aux q
									in aux liste
	|(Union liste) -> let rec aux l = match l with
								|[] -> ""
								|[h] -> ecrit h
								|h::q -> ecrit h ^ " U " ^ aux q
							in aux liste
	|(To (a, b)) -> "V" ^ ecrit a ^ "" ^ ecrit b
	|(Mo x) -> "f (" ^ ecrit x ^ ")"
	|(Bl x) -> x;;

let axiome G = match G with
	|(El x) -> snd x
	|_ -> [];;

let ecritaxiomes G = match G with
	|(El x) -> let rec aux l = match l with
							|[] -> ""
							|[h] -> ecrit h
							|h::q -> ecrit h ^ " puis " ^ aux q
							in (ecrit (El x)) ^ " verifie " ^ aux (snd x)
	|_ -> "";;

let ajout G ax = (El (ecrit G, ax :: (axiome G)));;

let inv (El x) = (In x);;

let e = El ("e", []);;
let e = ajout e neutre;;
let x = {nom = 0; appartenance = ["G"]};;
let y = {nom = 1; appartenance = ["G"]};;
let z = {nom = 2; appartenance = ["G"]};;
let a = {nom = 3; appartenance = ["Z"]};;
let b = {nom = 4; appartenance = ["Z"]};;
let c = {nom = 5; appartenance = ["Z"]};;

let neutre = To (Nn x, Eg [Op (Nn x, e); Op (e, Nn x); Nn x]);;
let associativiter = To (Nn x, To (Nn y, To (Nn z, Eg [Op (Op (Nn x, Nn y), Nn z); Op (Nn x, Op (Nn y, Nn z))])));;
let commutativiter H = To (Ap (Nn x, H), To (Ap (Nn y, H), Eg [Op (Nn x, Nn y); Op (Nn y, Nn x)]));;
let inverse H = To (Ap (Nn x, H), Ex (Ap (Nn y, H), Eg [Op (Nn x, Nn y); Op (Nn y, Nn x); e]));;
let stabiliter H = To (Ap (Nn x, H), To (Ap (Nn y, H), Ap (Op (Nn x, Nn y), H)));;
let monogene H = Ex (Ap (Nn a, H), To (Ap (Nn b, H), Ex (Ap (Nn c, H), Eg [Op (Nn a, Nn b); Nn c])));;
let stab_ker H = To (Ap (Nn x, H), To (Ap (Nn y, H), Im [Eg [Mo (Nn x); Mo (Nn y); e]; Eg [Mo (Op (Nn x, Nn y)); e]]));;
let stab_im H = To (Ap (Nn x, H), To (Ap (Nn y, H), Ex (Ap (Nn z, H), Eg [Mo (Op (Nn x, Nn y)); Nn z])));;
let stab_somme H F = To (Ap (Nn x, H), To (Ap (Nn y, F), To (Ap (Nn z, H), To (Ap (Nn a, F), Ex (Ap (Nn b, H), Ex (Ap (Nn c, F), Eg [Op (Op (Nn x, Nn y), Op (Nn z, Nn a)); Op (Nn b, Nn c)]))))));;

let sousgroupe G nom = 
	let H = ref (El (nom, [])) in
	H := ajout !H (stabiliter !H);
	H := ajout !H (inverse !H);
	!H;;

ecrit neutre;;
ecrit associativiter;;
ecrit (commutativiter G);;
ecrit (inverse G);;
ecrit (stabiliter G);;
ecrit (monogene G);;
ecrit (stab_ker H);;
ecrit (stab_im H);;
ecrit (stab_somme H F);;

let G = (El ("G", []));;
let G = ajout G associativiter;;
let Z = (El ("Z", []));;
let Z = ajout Z associativiter;;
let Z = ajout Z (commutativiter Z);;
let N = sousgroupe Z "N";;
let H = sousgroupe G "H";;
let F = sousgroupe G "F";;
let J = sousgroupe G "J";;
let R = (Intersection[F; H]);;
ecritaxiomes G;;

let redaction l = let rec aux l = match l with
	|[] -> ""
	|[h] -> ecrit h ^ " et c'est tout :)"
	|h::q -> ecrit h ^ " et que " ^ aux q
	in "On veut montrer que " ^ (aux l);;

let prefix &! a b = Et (a, b);;

let rec compil prop liste = match liste with
	|[] -> prop
	|(To (a, b))::q -> To (a, compil prop q)
	|(Ex (a, b))::q -> Ex (a, compil prop q)
	|x::q -> compil prop q;;

let rec check prop l = match l with
	|[] -> " piste nulle :("
	|h::q when h=prop -> " qui est un axiome :D"
	|h::q -> check prop q;;

let rec verifeg a b l = match l with
	|[] -> ""
	|(h::q) when (h=a || h=b)-> "x" ^ (verifeg a b q)
	|h::q -> verifeg a b q;;

let rec verifax a b ax = match ax with
	|[] -> false
	|(h :: q) -> match h with
					|(Eg l) -> if ("xx" = (verifeg a b (l))) then true else verifax a b q
					|_ -> verifax a b q;;






let axiomes = [inverse H; stabiliter H; inverse F; stabiliter F; inverse G; stabiliter G; commutativiter G; monogene Z];;

let aMq = [stabiliter (Intersection [H; F]); inverse (Intersection [H; F]); commutativiter J; monogene N; stab_ker G; stab_im G; stab_somme H F];;

let bb = (Bl "");;
let rec auxonne ax prop acc rien = match prop with
	|(Ex (Ap (a, H), To (Ap (b, G), z))) when (acc=[] && H=G)-> "On prends un " ^ (ecrit a) ^ " possible et on supp " ^ (ecrit (Ex (Ap (b, G), bb))) ^ " NON (" ^ (ecrit z) ^ ")" ^ " par stabiliter (" ^ (ecrit G) ^ " est un sous groupe) on a pgcd(" ^ (ecrit a) ^ ";" ^ (ecrit b) ^ ") qui appartient au groupe (par bezouth) : donc si on note d = pgcd(" ^ (ecrit a) ^ ";" ^ (ecrit b) ^ ") on a ici deux choix : soit d verifie la proposition auquel cas cqfd ^^, soit non, alors par recurrence finie (on est sur Z) decroissante, on obtient une contradiction, donc au bout d'un moment un d marchera et on aura " ^ (ecrit prop) ^ " avec " ^ (ecrit a) ^ " qui sera une iteration finie de pgcd, et donc un element du groupe"
	|(To (x, a)) when rien = 1 -> begin match x with
		|(Ap (y, (Intersection (H::[F])))) -> (ecrit a) ^ " qui est trivialement deduit de |[[[ " ^ (auxonne ax (compil (To (Ap (y, H), a)) (rev acc)) [] 0) ^ " OU " ^  (auxonne ax (compil (To (Ap (y, F), a)) (rev acc)) [] 0) ^ " ]]]|"
		|(Ap (y, H)) when H = (sousgroupe G "J") -> (ecrit a) ^ " qui est aisement (J inclus dans G) deductible de : " ^ (auxonne ax (compil (To (Ap (y, G), a)) (rev acc)) [] 0)
		|x -> auxonne ax a ((To (x, bb)) :: acc) 1
		|_ -> "boum" end
	|(Ex (x, a)) when rien = 1 -> begin match x with
		|(Ap (y, (Intersection (H::[F])))) -> (ecrit a) ^ " qui decoule de |[[[ " ^ (auxonne ax (compil (Ex (Ap (y, H), a)) (rev acc)) [] 0) ^ " OU " ^  (auxonne ax (compil (Ex (Ap (y, F), a)) (rev acc)) [] 0) ^ " ]]]|"
		|x -> auxonne ax a ((Ex (x, bb)) :: acc) 1
		|_ -> "boum" end
	|(Ap (x, G)) -> begin match G with
		|(Et (H, F)) -> "jack" (*auxonne ax (Ap (x, Intersection [H; F])) acc 0*)
		|(Intersection (H::[F])) -> (ecrit prop) ^ " <=> " ^ (auxonne ax (compil (Et (Ap (x, H), Ap (x, F))) (rev acc)) [] 0)(* ^ (auxonne ax (Et (Ap (x, H), Ap (x, F))) acc) *)
		|(El y) when rien = 1 -> (ecrit (Ap (x, G))) ^ (check (compil (Ap (x, G)) (rev acc)) axiomes)
		|(El y) -> (auxonne ax (compil (Ap (x, G)) (rev acc)) [] 1)(* ^ (check (compil (Ap (x, G)) (rev acc)) axiomes)*)(*ecrit (Ap (x, (El y)))*)
		|_ -> ":/" end
	|(Et (a, b)) -> (ecrit (Et (a, b))) ^ ": On veut mtn mq " ^ (ecrit (compil a (rev acc))) ^  " PUIS " ^ (ecrit (compil b (rev acc))) ^ ". Allons y : " ^ (auxonne ax (compil a (rev acc)) [] 0) ^  " ET ENFIN " ^ (auxonne ax (compil b (rev acc)) [] 0)
	|(Mo (Op (a, b))) -> (ecrit (Op (Mo (a), Mo (b)))) ^ " = " ^ (auxonne ax (compil (Op (Mo (a), Mo (b))) ([])) [] 0)
	|(Op (a, b)) when verifax a e ax -> (ecrit (Op ((Bl "e", b)))) ^ " = " ^ (auxonne ax b acc 0)
	|(Op (a, b)) when verifax b e ax -> (ecrit (Op ((a, Bl "e")))) ^ " = " ^ (auxonne ax a acc 0)
	|(Op (a, b)) -> "par stabiliter " ^ ecrit (Ex (Ap (Nn c, G), Eg [Op (a, b); Nn c]))
	|x when verifax x e ax -> auxonne ax (compil e (rev acc)) [] 0
	|(To (x, a)) -> (ecrit (To (x, bb))) ^ (auxonne ax a ((To (x, bb)) :: acc) 0)
	|(Ex (x, a)) -> (ecrit (Ex (x, bb))) ^ (auxonne ax a ((Ex (x, bb)) :: acc) 0)
	|(Eg l) when rien = 0 -> let jacky li = match li with
										|h::[q] -> ".Mq " ^ (ecrit h) ^ " = " ^ (ecrit q) ^ " : on a " ^ (ecrit h) ^ "=" ^ (auxonne ax h acc 0) ^ " = " ^ (auxonne ax q acc 0) ^ " et c'est la meme chose :o"
										|_ -> "jacky" in jacky l
	|(Eg l) when rien = 1 -> (ecrit (Eg l)) ^ check (compil (Eg l) (rev acc)) axiomes
	|(Eq (a :: [b])) -> " par double implication : => " ^ (auxonne (a::ax) b acc 0) ^ "puis <= :" ^ (auxonne (b::ax) a acc 0) ^ "et voila ^^"
	|(Im (a :: [b])) -> (ecrit a) ^ " et on veut montrer " ^ (ecrit b) ^ " allons y de ce pas" ^ (auxonne (a::ax) b acc 0)
	|(El j) when (fst j)="e" -> "e"
	|x -> ecrit x(*(auxonne ax (compil prop (rev acc)) [] 1)*);;

let biatch liste = let rec b2 liste = match liste with
	|[] -> "Mec la liste est vide, t'as pas un truc plus dur ^^ ?"
	|h :: q -> "Montrons " ^ (ecrit h) ^ " on a : " ^ (auxonne axiomes h [] 0) ^ " OU " ^ (auxonne axiomes h [] 1) ^ " cqfd :p. Allons y proprieter suivante :                                                                                                                                                                             ~                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    ~                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      "^ (b2 q) in (redaction liste) ^ "                                                                                                                                                                             **                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    **                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      **                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      " ^ (b2 liste);;

biatch aMq;;
