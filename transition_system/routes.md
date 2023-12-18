
# Route requests

## Route QR100(M)

    *QR100(M)                      /to S102
            if R100(M) a
            then R100(M) s
                 UAB-BA l
            \ 
    \

The transition system is:

    not erel
    "QR100(M)" : request
    "R100(M)" : route_a
    -->
    route_s' = route_s \/ {"R100(M)"}
    subroute_l' = subroute_l \/ {"UAB-BA"}


## Route R102A(M)

    *QR102A(M)                      /to S110
            if R102A(M) a
               P100 cfr  P110 cfn
            then R102A(M) s
                 UAC-CA l  UAD-DA l
                 P100 cr  P110 cn
            \
    \

The transition system is:

    not erel
    "QR102A(M)" : request
    "R102A(M)" : route_a
    point_state(P100) = REVERSE or (TAC : track_c and "UAC-AD" : subroute_l and "UAC-DA" : subroute_l and "UAC-CB" : subroute_l and "UAC-BC" : subroute_l)
    point_state(P110) = NORMAL or (TAD : track_c and " UAC-BD" : subroute_l and "UAC-DB" : subroute_l)
    -->
    route_s' = route_s \/ {"R102A(M)"}
    subroute_l' = subroute_l \/ {"UAC-CA", "UAD-DA"}
    point_state' = point_state <+ {P100 -> REVERSE, P110 -> NORMAL}


## Route R102B(M)

    *QR102B(M)                      /to S104
            if R102B(M) a
               P100 cfn  P110 cfn
            then R102B(M) s
                 UAC-CB l  UAD-CB l  UAF-BA l
                 P100 cn  P110 cn
            \
    \


The transition system is:

    not erel
    "QR102B(M)" : request
    "R102B(M)" : route_a
    point_state(P100) = NORMAL or (TAC : track_c and "UAC-AC" : subroute_l and "UAC-CA" : subroute_l)
    point_state(P110) = NORMAL or (TAD : track_c and " UAC-BD" : subroute_l and "UAC-DB" : subroute_l)
    -->
    route_s' = route_s \/ {"R102B(M)"}
    subroute_l' = subroute_l \/ {"UAC-CB", "UAD-CB", "UAF-BA"}
    point_state' = point_state <+ {P100 -> NORMAL, P110 -> NORMAL}
