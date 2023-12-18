# Properties

## Sub route setting on route set

Whenever a route is set, all associated route locking is applied by sub routes.

Semi-formal statement:

    [for]
        every set route
    [it holds that]
        all sub routes of the route that are within the interlocking's control area are locked

Formal statement

    forall r:Route 
       r:cover(route_s \ "route_s'p")
       =>
       (forall sr:SubRoute
                 sr: "route:subrouteset"[{r}] /\ "SubRoute.ixl"
                 =>
                 sr: subroute_l
		)


## Alignment of sub route locking with points (normal)

Whenever a sub route is locked over points in their normal lie, those points are commanded normal.


Semi-formal statement:

    [for]
        every sub route locking command Uxx l for a sub route within the interlocking area
    [it holds that]
        every point that must be set normal to enable sub route path is commanded normal Pzz cn


Formal statement

    forall sr: SubRoute
        sr : cover(subroute_l \ subroute_l'p) /\ "SubRoute.ixl"
      =>
        # all sub route normal points are commanded normal
        forall p: Node
            p: "Node.base"["subroute:pointnormal"[{sr}]] 
          => 
            point_c(p) == NORMAL
