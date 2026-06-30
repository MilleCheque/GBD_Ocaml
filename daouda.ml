(************************** LES TYPES *****************************)

type dbtype =
  | TInt  
  | TText 

type coltype = dbtype * bool 

type dbvalue =
  | VInt of int      
  | VText of string 
  | VNull           

type schema = (string * coltype) list 
type row = dbvalue list 
type table = { cols : schema; rows : row list } 
type fd = (string list) * (string list) 

(*********************** FONCTIONS AUXILIAIRES **********************)

(*
type : 'a -> 'a list -> bool
@requires : aucune
@ensures : renvoie true si x est présent dans lst, false sinon
@raises : aucune
*)
let rec elmt_in_lst x lst = match lst with
    | [] -> false
    | y::lst' -> if y = x then true else elmt_in_lst x lst' 

(*
type : 'a -> 'a list list -> 'a list list
@requires : aucune
@ensures : renvoie une liste de listes où x a été ajouté en tête de chaque sous-liste de lst
@raises : aucune
*)
let rec ajoute_au_ensembles x lst = match lst with
    | [] -> [[x]]
    | l1::rest -> (x::l1) :: (ajoute_au_ensembles x rest)

(*
type : 'a -> 'a list list -> bool
@requires : aucune
@ensures : renvoie true ssi x est présent dans au moins une des sous-listes de lsts
@raises : aucune
*)
let rec est_dans_ss_ens x lsts = match lsts with
    | [] -> false
    | l::lsts' -> if elmt_in_lst x l then true else est_dans_ss_ens x lsts'

(*
type : 'a list -> 'a list -> bool
@requires : aucune
@ensures : renvoie true ssi tous les éléments de lst1 sont dans lst2 (inclusion au sens large)
@raises : aucune
*)
let rec test_inclusion lst1 lst2 = match lst1 with
    | [] -> true
    | s::lst' -> if (elmt_in_lst s lst2) then (test_inclusion lst' lst2) else false

(*
type : 'a list -> 'a list list -> bool
@requires : aucune
@ensures : renvoie true ssi la liste l est incluse dans au moins une des listes de lsts
@raises : aucune
*)
let rec inclue_dans1_ssens l lsts = match lsts with
    | [] -> l = [] 
    | l2::lsts' -> if test_inclusion l l2 then true else inclue_dans1_ssens l lsts'

(*
type : 'a list -> 'a list list -> bool
@requires : aucune
@ensures : renvoie true ssi l est incluse dans une liste de lsts ET que sa taille est strictement inférieure
@raises : aucune
*)
let rec incluestrict_dans1_ssens l lsts = match lsts with
    | [] -> false
    | l2::lsts' ->
        if test_inclusion l l2 && List.length l < List.length l2 then true
        else incluestrict_dans1_ssens l lsts'

(*
type : table -> bool
@requires : aucune
@ensures : renvoie true si toutes les lignes de la table sont structurellement identiques
@raises : aucune
*)
let test_same_lignes { cols = _; rows = lgns } =
    match lgns with
    | [] -> true
    | l0::rest -> List.for_all (fun x -> x = l0) rest

(*
type : 'a list -> 'a list list
@requires : aucune
@ensures : renvoie l'ensemble des parties de la liste lst (sans l'ensemble vide)
@raises : aucune
*)
let rec get_ensemble_elmt lst = match lst with
    | [] -> [] 
    | [t] -> [[t]]
    | t::q -> 
        let reste = get_ensemble_elmt q in
        [t] :: reste @ (ajoute_au_ensembles t reste)

(*
type : 'a list -> 'a list
@requires : aucune
@ensures : renvoie la liste privée de ses doublons (préserve l'ordre de première apparition)
@raises : aucune
*)
let supp_doublon_lst lst = 
    let rec aux l acc = match l with
        | [] -> List.rev acc
        | x::lst' -> if elmt_in_lst x acc then aux lst' acc else aux lst' (x::acc)
    in aux lst []

(*
type : 'a list -> 'a list -> bool
@requires : aucune
@ensures : renvoie true si au moins un élément de lst1 est présent dans lst2
@raises : aucune
*)
let rec contient_elemt_of lst1 lst2 = match lst1 with
    | [] -> false
    | x::lst1' -> if elmt_in_lst x lst2 then true else contient_elemt_of lst1' lst2


(*
type : 'a -> 'a list -> 'a list
@requires : aucune
@ensures : renvoie la liste privée de toutes les occurrences de x
@raises : aucune
*)
let rec lst_sans x lst = List.filter (fun y -> y <> x) lst


(***************************** PARTIE 1 ************************************)


exception Table_non_carre 
exception Table_Erreur_Typage
exception Tentative_ajout_ligne_imcompatible
exception Argument_Invalides
exception Table_invalide

(*
type : (string * coltype) -> schema -> row -> dbvalue
@requires : la colonne x existe dans le schéma schema_list et la ligne row_list a la même taille
@ensures : renvoie la valeur dbvalue correspondant à la colonne x dans la ligne donnée
@raises : Argument_Invalides si les listes sont de tailles différentes ou si la colonne n'est pas trouvée
*)
let rec elmt_of_type x schema_list row_list = 
    match schema_list, row_list with
    | (name, _)::s_rest, v::r_rest -> if name = fst x then v else elmt_of_type x s_rest r_rest
    | [], [] -> raise Argument_Invalides
    | _, _ -> raise Argument_Invalides

(*
type : row -> schema -> bool
@requires : aucune
@ensures : renvoie true ssi la ligne respecte le typage et les contraintes et  NULL du schéma
@raises : Table_non_carre si la ligne n'a pas le bon nombre de cellules, Table_Erreur_Typage si un type diverge
*)
let rec check_ligne_table l c = match l,c with
    | [], [] -> true
    | [], _ | _, [] -> raise Table_non_carre
    | e::l',((_,(t,b))::c') ->
        let valid = match e, t with
            | VNull, _ -> b
            | VText _, TText -> true
            | VInt _, TInt  -> true
            | _ -> false
        in if valid then check_ligne_table l' c' else raise Table_Erreur_Typage

(*
type : table -> bool
@requires : aucune
@ensures : true ssi toutes les lignes de la table sont valides vis-à-vis du schéma
           (cad que elles ont un element pour chaque colonne et un element est null seulement si il est dans une colonne qui l'autorise)
@raises : Table_non_carre ou Table_Erreur_Typage via check_ligne_table
*)
let rec check_table { cols = c; rows = lgns } = match lgns with
    | [] -> true
    | l::lsgns -> check_ligne_table l c && check_table { cols = c; rows = lsgns }

(*
type : table -> row -> table
@requires : table bien formée
@ensures : renvoie une nouvelle table avec la ligne r ajoutée en tête
@raises : Tentative_ajout_ligne_imcompatible si la ligne ne respecte pas le schéma
*)
let insert { cols = c; rows = lgns } r =
  try
    if check_ligne_table r c then { cols = c; rows = r :: lgns }
    else raise Tentative_ajout_ligne_imcompatible
  with _ -> raise Tentative_ajout_ligne_imcompatible

(*
type : table -> table -> table
@requires : deux tables bien formées
@ensures : calcule le produit cartésien des lignes et concatène les schémas
@raises : aucune
*)
let prod {cols = c1; rows = lgns1} {cols = c2; rows = lgns2} = 
    let c = c1 @ c2 in
    let rec aux l1 l2_list acc = match l2_list with
        | [] -> acc
        | l2::l2_list' -> aux l1 l2_list' ((l1 @ l2) :: acc)
    in
    let lignes = List.fold_right (fun l1 acc -> aux l1 lgns2 acc) lgns1 [] in
    { cols = c; rows = lignes }

(*
type : schema -> schema -> row -> row
@requires : c2 est un sous-ensemble du schéma global c
@ensures : extrait les valeurs de la ligne lgn correspondant aux colonnes de c2
@raises : Argument_Invalides via elmt_of_type
*)
let projection_ligne c2 c lgn = List.map (fun c2' -> elmt_of_type c2' c lgn) c2

(*
type : table -> schema -> table
@requires : c2 est un sous-ensemble du schéma de la table
@ensures : renvoie la table projetée sur les colonnes de c2
@raises : Table_invalide si une colonne de c2 est absente
*)
let projection { cols = c; rows = lgns } c2 =
    if c2 = [] then { cols = []; rows = [] } 
    else try { cols = c2; rows = List.map (projection_ligne c2 c) lgns }
         with _ -> raise Table_invalide

(*
type : table -> (row -> bool) -> table
@requires : aucune
@ensures : renvoie la table contenant uniquement les lignes validant le prédicat test
@raises : aucune
*)
let restrict { cols = c; rows = lgns } test =
    { cols = c; rows = List.filter test lgns }


(********************************** PARTIE 2 ********************************)


(*
type : schema -> string list
@requires : aucune
@ensures : extrait la liste des noms des colonnes à partir du schéma
@raises : aucune
*)
let rec lst_col_to_lst_str lst = List.map fst lst


(*
type : schema -> schema -> table -> (schema * schema)
@requires : cols1 et cols2 sous-ensembles du schéma de la table
@ensures : renvoie (cols1, cols2) si la DF cols1 -> cols2 est vérifiée, sinon ([], [])
@raises : aucune
*)
let donne_dependance cols1 cols2 ({ cols = c; rows = lgns } as tab) = 
    let valeurs_uniques = supp_doublon_lst (List.map (fun l -> projection_ligne cols1 c l) lgns) in
    let aux_verif_lignes = List.for_all (fun lgn1 ->
        let f_test li = (projection_ligne cols1 c li) = lgn1 in
        let tab_restreinte = restrict tab f_test in
        let tab2 = projection tab_restreinte cols2 in
        test_same_lignes tab2
    ) valeurs_uniques in
    if aux_verif_lignes then (cols1, cols2) else ([], [])

(*
type : schema -> schema list -> table -> (schema * schema) list -> (schema * schema) list
@requires : aucune
@ensures : accumule les dépendances fonctionnelles trouvées entre cols et les éléments de ss_colonnes
@raises : aucune
*)
let rec ajoute_dependance cols ss_colonnes tab acc = match ss_colonnes with
    | [] -> (cols, cols) :: acc
    | cols1 :: ss_colonnes' -> 
        let d1 = donne_dependance cols1 cols tab in
        let d2 = donne_dependance cols cols1 tab in
        ajoute_dependance cols ss_colonnes' tab (d1 :: d2 :: acc)

(*
type : table -> (schema * schema) list
@requires : table bien formée
@ensures : calcule toutes les dépendances fonctionnelles valides entre sous-ensembles de colonnes
@raises : aucune
*)
let compute_deps_col ({ cols = c; rows = lgns } as tab) =
    if c = [] || lgns = [] then [([], [])] else
    let ss_colonnes = get_ensemble_elmt c in
    let rec aux ens_list acc = match ens_list with
        | [] -> acc
        | ens :: reste -> 
            let nouvelles_deps = ajoute_dependance ens reste tab acc in
            aux reste nouvelles_deps
    in
    supp_doublon_lst (List.filter (fun (a,b) -> a <> [] && b <> []) (aux ss_colonnes []) )

(*
type : table -> (string list * string list) list
@requires : aucune
@ensures : identique à compute_deps_col mais retourne uniquement les noms de colonnes
@raises : aucune
*)
let compute_deps tab = List.map (fun (l1,l2) ->
    (lst_col_to_lst_str l1, lst_col_to_lst_str l2)) (compute_deps_col tab)

(*
type : table -> (string * string) list
@requires : table bien formée
@ensures : calcule toutes les dépendances fonctionnelles élémentaires valides
@raises : aucune
*)
let compute_elementary_deps ({ cols = c; rows = lgns } as tab) =
    let deps = compute_deps tab in
    List.filter (fun (l1,l2) -> match l1 with
        |[x] -> true
        |_ -> false
    )deps

(*
type : table -> schema list
@requires : aucune
@ensures : renvoie la liste de toutes les super-clés de la table
@raises : aucune
*)
(*on chercher les liste de colonne X telle que on a la dépendance X->C avec C les colonnes du tableau*)
let donne_cle ({ cols = c; _ } as tab) =
    let n = List.length c in
    let deps = compute_deps_col tab in
    supp_doublon_lst (
        List.fold_left (fun acc (l1, l2) -> 
            if List.length l2 = n && l1 <> [] then l1 :: acc else acc
        ) [] deps
    )

(*
type : table -> schema list
@requires : aucune
@ensures : renvoie les clés candidates (super-clés minimales)
@raises : aucune
@IDEE : guarder parmis les super_cles celle pour qui il n'existe pas de clé inclue strictement dedans
        puis guarder parmis ces cles celles ou aucune colonne ne permet Vnull
*)
let donne_cle_cand tab =
    let cles = donne_cle tab in
    let filtre_cle1 candidat = 
    (*On guarde les clé minimal*)
        List.filter (fun c ->  
            not (List.exists (fun autre -> test_inclusion autre c && List.length autre < List.length c) cles)
        ) candidat
    in 
    let filtre_cle2 candidat = 
         List.filter ( fun c ->
            (*on guarde que le bool qui dit si VNull est permis dans la liste de colonne *)
            let c' = List.map (fun x -> snd (snd x)) c in
            not (elmt_in_lst true c') 
         ) candidat
    in
    supp_doublon_lst (filtre_cle2 (filtre_cle1 cles))

(*
type : table -> bool
@requires : aucune
@ensures : true ssi la table est en 1ère Forme Normale (bien formée et possède une clé)
@raises : aucune (capte les exceptions de check_table)
*)
let test_1NF tab = 
  try 
    check_table tab && donne_cle_cand tab <> []
  with _ -> false

(*
type : table -> schema
@requires : aucune
@ensures : renvoie la liste des colonnes n'appartenant à aucune clé candidate
@raises : aucune
*)
let donne_attributs_non_cle ({ cols = c; rows = _ } as tab) =
    let cle_cands = donne_cle_cand tab in
    let aux col = 
        let appartient_a_une_cle = List.exists (fun cle -> elmt_in_lst col cle) cle_cands in
        not appartient_a_une_cle
    in
    List.filter aux c

(*
type : table -> bool
@requires : aucune
@ensures : true ssi aucun attribut non-clé ne dépend d'une partie d'une clé candidate
@raises : aucune
*)
let test_non_dep_partielle tab = 
    let cle_cands = donne_cle_cand tab in
    let deps = compute_deps_col tab in
    let att_noncle = donne_attributs_non_cle tab in
    let rec aux deps = match deps with
        |[] -> true
        |(x,y)::deps' ->
        if contient_elemt_of y att_noncle
            then if incluestrict_dans1_ssens x cle_cands then false
            else aux deps'
        else aux deps' in
    aux deps

(*
type : table -> bool
@requires : aucune
@ensures : vérifie si la table est en 2NF
@raises : aucune
*)
let test_2NF tab = test_1NF tab && test_non_dep_partielle tab

(*
type : table -> bool
@requires : aucune
@ensures : true ssi aucun attribut non-clé ne dépend transitivement d'une clé
@raises : aucune
*)
let test_non_dep_transitive tab =
    let cles = donne_cle tab in
    let deps = compute_deps_col tab in
    let att_noncle = donne_attributs_non_cle tab in
    List.for_all (fun (x, y) ->
        if not (elmt_in_lst x cles) && contient_elemt_of y att_noncle then false else true
    ) deps

(*
type : table -> bool
@requires : aucune
@ensures : vérifie si la table est en 3NF
@raises : aucune
*)
let test_3NF tab = test_2NF tab && test_non_dep_transitive tab

(*
type : table -> int
@requires : aucune
@ensures : renvoie l'entier (0, 1, 2 ou 3) représentant le niveau de normalisation
@raises : aucune
*)
let normalization_level tab = 
    if test_3NF tab then 3 
    else if test_2NF tab then 2 
    else if test_1NF tab then 1 
    else 0