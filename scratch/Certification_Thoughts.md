# Thoughts on certifying the results of the exact-arithmetic spanning tree modulus solver

## The duality statement
Let $\rho\in\text{Adm}(\Gamma)$ and $\mu\in\mathcal{P}(\Gamma)$. Then

$$
\left<\rho,\mathcal{N}^T\mu\right> = \left<\mathcal{N}\rho,\mu\right> \ge 1.
$$
So, by Cauchy-Schwarz
$$
1 \le \left<\rho,\mathcal{N}^T\mu\right> \le \|\rho\|\,\|\mathcal{N}^T\mu\|.
$$
This immediately shows weak duality:
$$
\inf_{\rho\in\text{Adm}(\Gamma)}\|\rho\|^2\cdot\inf_{\mu\in\mathcal{P}(\Gamma)}\|\mathcal{N}^T\mu\|^2 \ge 1.
$$
If we can find choices for $\rho$ and $\mu$ that make the inequality hold as equality, then both choices are necessarily optimal for their respective problems.

To understand the equality case, let $\eta = \mathcal{N}^T\mu$. Equality in Cauchy-Schwarz can only hold if the vectors are parallel: $\rho = \alpha\eta$. Plugging that into the inequality shows that
$$
1 = \left<\alpha\eta,\eta\right> = \alpha\|\eta\|^2,
$$
so $\alpha = \|\eta\|^{-2}$.

## Certifying the results of the exact-arithmetic spanning tree modulus solver

### Modifications to the solver
The solver needs to output some additional data (either signaled by a flag, or just default behavior). Essentially, we need to know exactly which edges were dispatched at each round of the algorithm. Just that should be enough to build the certificate. This report should probably be versioned to allow for format changes going forward.

### Certificate builder
The certificate builder needs to take the step-wise output of the solver and produce a certificate. The certificate should be versioned so that we know how to handle different certificate versions. The certificate builder's primary job will be to construct the pmf on spanning trees; everything else comes from there. This will be a little tricky because we want to avoid combinatorial blow-up. Fortunately, Carathéodory's theorem will rescue us here.

#### Local constructions
Whenever a set of edges is processed by the modulus solver, they define a vertex partition. The main bookkeeping problem will be to keep track of components as the algorithm progresses (see below). For now, suppose we know the graph we're working with and the set, $C\subseteq E$ of edges that the solver dispatched. Removing those edges from the graph leaves 2 or more connected components; that's the vertex partition. If each of those components is shrunk to a single vertex and self-loops are discarded, we end up with a shrunk multigraph $\tilde{G}=(\tilde{V},C)$.

**Medium gap:** From modulus theory, we know that there is a pmf on the spanning trees of $\tilde{G}$ that give every edge identical edge usage $(|\tilde{V}|-1)/|C|$. The trick is finding it. Since we're in $|C|$-dimensional space, there should be an optimal pmf on no more than $|C|+1$ spanning trees. We'll need to figure out how to construct that.

Once that's decided, the edges $C$ are discarded, leaving some connected components. The trivial components with no edges can be ignored. The rest are put into a queue and processed in the same way. There will need to be some bookkeeping or searches to find the queued graph that corresponds to the current set of edges. Everything here is in rational arithmetic with controlled denominators, so the real issue is just knowing how to record the pmfs and how big of a graph we can actually certify.

#### Global gluing
Once finished, I think we can build the full pmf. We just need a pmf whose marginals behave as expected on each of the sets of $C$ we've processed. We should be able to do that by a simple gluing argument. The end result will be a pmf on spanning trees that should be optimal for the problem above.

#### What else to compute
At a minimum, the certificate builder should build the pmf. However, since we can write this part with simple, untrusted code, it probably makes sense to elaborate a lot more of the results, leaving less for the formal verifier to verify. Two other things that might be valuable are the corresponding expected edge usages, $\eta = \mathcal{N}^T\mu$ along with the proposed optimal density $\rho$. The latter is simply $\rho=\eta/\|\eta\|^2$. I'm not sure if these are worthwhile or not, since the verifier probably needs to construct them anyway.

## The verifier

The verifier seems to need two components:

### The duality theorem from above
Essentially, it needs to know that if we can demonstrate that $\mu$ and $\rho$ are admissible and that the product of their energies is one, then both are optimal. This just has to be proved once.

### The explicit verification
This needs to take the specific values from the certificate builder and verify the arithmetic.

**Biggest Gap:** Admissibility of $\rho$ is the hardest part here. I don't think it's actually in reach for the first attempt. One possibility is to implement Kruskal with no proof and to define admissibility as having the property that the minimum spanning tree length returned by Kruskal is $\ge 1$. Essentially, this assumes that the Kruskal result implies $\mathcal{N}\rho\ge 1$ which isn't horrible for a first pass. I'm not sure how to make this kind of thing clean in Lean, though.