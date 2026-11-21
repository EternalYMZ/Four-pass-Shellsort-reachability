# Can all keys follow individually feasible paths?

With odd $m\ge5$, set $n=2m$ and use gaps $(m,4,2,1)$. The first pass partitions the slots into pairs. Individual paths to later destinations can compete for a slot or require opposite outcomes of one comparison.

Assign a potential $U(x,i)$ to key $x$ in slot $i$. If a one-step move at an allowed gap changes a key's potential by at most one, an elementary exchange representing a successful shift changes the total by at most two. Choose potentials separately before and after a checkpoint. Every slot there holds exactly one key. If keys in a set $T$ can avoid an extra cost only in slots $S$, then at least $|T|-|S|$ keys pay it whenever $|T|>|S|$. Adding this penalty to the potential differences bounds actual shifts. For $(2,0,3,1)$ and gaps $(2,1)$ a four-slot certificate gives a lower bound of three, attained by the final pass.

For the four-pass family on uniform inputs, individual reachability plus one key per slot gives a relaxed assignment bound of zero on final-pass shifts. Allowing rank-informed orientations of the first pairs followed by ordinary gaps 4 and 2 gives an optimal mean final-pass cost of order $n$. Restoring the actual first comparisons gives order $n^{3/2}$. The general potential inequality and four-slot certificate are formalized; the full three-way comparison is analytical.

[SlotCollisionPenalty.lean](https://github.com/EternalYMZ/Four-pass-Shellsort-reachability/blob/f9c50e72c0bd6a3496b86e5c9d02acd86a8cb805/Shellsort/SlotCollisionPenalty.lean) · [FourSlotExample.lean](https://github.com/EternalYMZ/Four-pass-Shellsort-reachability/blob/f9c50e72c0bd6a3496b86e5c9d02acd86a8cb805/FourSlotExample.lean)
