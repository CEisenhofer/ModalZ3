(declare-sort Relation 0)
(declare-sort World 0)

(declare-const r1 Relation)

(declare-fun Var!1898 (World) Bool)
(declare-fun Var!1899 (World) Bool)

(declare-fun world!1916 () World)
(declare-fun world!1917 () World)
(declare-fun world!1918 () World)

(declare-fun reachable (Relation World World) Bool)


(or (forall ((world!1917 World))
                 (! (=> (reachable r1 world!1916 world!1917)
                        (not (Var!1898 world!1917)))
                    :weight 0))
    (not (Var!1898 world!1916))
    (Var!1898 world!1916)
    (Var!1898 world!1916)
    (not (Var!1899 world!1916))
    (Var!1898 world!1916)
    (forall ((world!1918 World))
      (=> (reachable r1 world!1916 world!1918) false)))

(check-sat)
(get-model)
