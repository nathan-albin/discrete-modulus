import LeanModulus.Common.GraphicMatroid
import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.Combinatorics.Matroid.Minor.Restrict

open scoped Matroid

namespace Multigraph

variable {V E : Type*} [Finite E] (G : Multigraph V E)

/-- A spanning tree is exactly a base of the graphic matroid, provided `G`
itself (using all of its edges) is connected. Without connectivity of `G`
this is false in one direction: a maximal forest of a disconnected `G` is a
spanning *forest*, one tree per component, not a single spanning tree
touching every vertex. -/
theorem isSpanningTree_iff_isBase (hGconn : (G.toSimpleGraph Set.univ).Connected) {T : Set E} :
    G.IsSpanningTree T ↔ G.graphicMatroid.IsBase T := by
  constructor
  · rintro ⟨hforest, hconn⟩
    rw [← graphicMatroid_indep] at hforest
    refine hforest.isBase_of_maximal fun J hJ hTJ => ?_
    by_contra hne
    obtain ⟨e, heJ, heT⟩ := Set.exists_of_ssubset (hTJ.lt_of_ne hne)
    obtain ⟨hJloop, hJinj, hJacyc⟩ := G.graphicMatroid_indep.mp hJ
    induction huv : G.endpoints e using Sym2.ind with
    | _ u v =>
    have hne_uv : u ≠ v := by
      rintro rfl
      exact hJloop e heJ (huv ▸ Sym2.mk_isDiag_iff.mpr rfl)
    have hTsub : T ⊆ J \ {e} := Set.subset_sdiff_singleton hTJ.subset heT
    have hreachT : (G.toSimpleGraph T).Reachable u v := hconn.1 u v
    have hreachJe : (G.toSimpleGraph (J \ {e})).Reachable u v :=
      hreachT.mono (SimpleGraph.fromEdgeSet_mono (Set.image_mono hTsub))
    have hnadjJe : ¬ (G.toSimpleGraph (J \ {e})).Adj u v := by
      rw [Multigraph.toSimpleGraph, SimpleGraph.fromEdgeSet_adj]
      rintro ⟨⟨e', ⟨he'J, he'ne⟩, he'uv⟩, -⟩
      exact he'ne (hJinj he'J heJ (he'uv.trans huv.symm))
    have hJeq : J = insert e (J \ {e}) := by
      rw [Set.insert_sdiff_singleton, Set.insert_eq_self.mpr heJ]
    have himg : G.endpoints '' J = G.endpoints '' (J \ {e}) ∪ {s(u, v)} := by
      conv_lhs => rw [hJeq]
      rw [Set.image_insert_eq, Set.insert_eq, huv, Set.union_comm]
    have hsplit : G.toSimpleGraph J = G.toSimpleGraph (J \ {e}) ⊔ SimpleGraph.edge u v := by
      rw [Multigraph.toSimpleGraph, Multigraph.toSimpleGraph, himg, SimpleGraph.fromEdgeSet_union]
      rfl
    have hnotacyc : ¬ (G.toSimpleGraph (J \ {e}) ⊔ SimpleGraph.edge u v).IsAcyclic := by
      rw [SimpleGraph.isAcyclic_sup_fromEdgeSet_iff]
      push Not
      intro _
      exact ⟨hreachJe, fun h => (hne_uv h).elim, hnadjJe⟩
    rw [← hsplit] at hnotacyc
    exact hnotacyc hJacyc
  · intro hbase
    have hforest : G.IsForest T := G.graphicMatroid_indep.mp hbase.indep
    have hmax : Maximal G.graphicMatroid.Indep T := Matroid.isBase_iff_maximal_indep.mp hbase
    haveI := hGconn.nonempty
    refine ⟨hforest, ⟨fun u v => ?_⟩⟩
    refine SimpleGraph.reachable_le_of_adj_le (fun x => SimpleGraph.Reachable.refl x)
      (fun _ _ _ a b => a.trans b) ?_ u v (hGconn.1 u v)
    intro x y hadj
    rw [Multigraph.toSimpleGraph, SimpleGraph.fromEdgeSet_adj] at hadj
    obtain ⟨⟨e, -, hexy⟩, hne⟩ := hadj
    by_cases heT : e ∈ T
    · refine SimpleGraph.Adj.reachable ?_
      rw [Multigraph.toSimpleGraph, SimpleGraph.fromEdgeSet_adj]
      exact ⟨⟨e, heT, hexy⟩, hne⟩
    · by_contra hnr
      have hins : G.IsForest (insert e T) :=
        IsForest.insert_of_not_reachable G hforest heT hexy hne hnr
      have hlt : T ⊂ insert e T := Set.ssubset_insert heT
      exact heT (hmax.2 (G.graphicMatroid_indep.mpr hins) hlt.subset (Set.mem_insert e T))

/-- The gluing fact behind assembling a spanning tree of `G` out of a
spanning tree of one vertex block plus a spanning tree of the rest of the
graph with that block contracted to a point: given a spanning tree `I` of
the induced subgraph on edge set `A`, and a spanning tree `J` of the
contraction of `G.graphicMatroid` by `I`, the union `J ∪ I` is a spanning
tree of the whole graph. Purely a specialization of Mathlib's general
matroid restriction/contraction API
(`Matroid.Indep.union_isBasis_union_of_contract_isBasis`) -- no new
graph-theoretic reasoning needed. -/
theorem isBase_union_of_isBase_restrict_isBase_contract
    {A I J : Set E}
    (hI : (G.graphicMatroid ↾ A).IsBase I)
    (hJ : (G.graphicMatroid ／ I).IsBase J) :
    G.graphicMatroid.IsBase (J ∪ I) := by
  have hIbasis : G.graphicMatroid.IsBasis' I A := Matroid.isBase_restrict_iff'.mp hI
  have hIindep : G.graphicMatroid.Indep I := hIbasis.indep
  have hJbasis : (G.graphicMatroid ／ I).IsBasis J (G.graphicMatroid ／ I).E :=
    Matroid.isBasis_ground_iff.mpr hJ
  have hunion := hIindep.union_isBasis_union_of_contract_isBasis hJbasis
  have hEeq : (G.graphicMatroid ／ I).E ∪ I = G.graphicMatroid.E := by
    rw [Matroid.contract_ground, graphicMatroid_E, Set.sdiff_union_of_subset (Set.subset_univ I)]
  rw [hEeq, Matroid.isBasis_ground_iff] at hunion
  exact hunion

end Multigraph
