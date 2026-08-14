import GaloisForLFunctions.HTGeometry.WeightedComplexLink
import GaloisForLFunctions.HTGeometry.SimplicialLinkRestrict

/-!
# Garland's localization: the mass norm

Garland's method compares a cochain with its restrictions to the links of the faces one dimension
below.  The first half of the comparison is the norm identity: summing the mass norm of the link
restriction over all faces of dimension `k - 1` recovers the mass norm of the cochain, up to the
factor `(n - k)(k + 1)` — the weighted degree of a vertex in a link, times the number of vertices of
a face.

The counting behind it is that the pairs `(σ, u)` with `|σ| = k` and `u ∉ σ` are the pairs `(τ, u)`
with `|τ| = k + 1` and `u ∈ τ`.

* `sum_powersetCard_insert` : **that counting, as an identity of sums.**
* `cochainNormSq` : the mass norm of a cochain in a fixed degree.
* `link_massInner_eq` : the mass norm of a link restriction, in terms of the complex.
* `sum_link_massInner` : **the link mass norms add up to `(n - k)(k + 1)` times the mass norm.**
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

variable {V : Type*} [DecidableEq V] [LinearOrder V] [Fintype V]

omit [LinearOrder V] in
/-- **Faces of one higher dimension, counted with their vertices.**  Summing a function of a face
and one of its vertices over all `(σ, u)` with `|σ| = k` and `u ∉ σ` is the same as summing over all
`(τ, u)` with `|τ| = k + 1` and `u ∈ τ`. -/
theorem sum_powersetCard_insert (k : ℕ) (G : Finset V → V → ℝ) :
    ∑ σ ∈ (univ : Finset V).powersetCard k, ∑ u ∈ univ \ σ, G σ u
      = ∑ τ ∈ (univ : Finset V).powersetCard (k + 1), ∑ u ∈ τ, G (τ.erase u) u := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => (⟨insert x.2 x.1, x.2⟩ : (_ : Finset V) × V))
    (fun y => (⟨y.1.erase y.2, y.2⟩ : (_ : Finset V) × V)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨σ, u⟩ hx
    rw [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff] at hx
    rw [Finset.mem_sigma, Finset.mem_powersetCard]
    exact ⟨⟨Finset.subset_univ _, by rw [Finset.card_insert_of_notMem hx.2.2, hx.1.2]⟩,
      Finset.mem_insert_self _ _⟩
  · rintro ⟨τ, u⟩ hy
    rw [Finset.mem_sigma, Finset.mem_powersetCard] at hy
    rw [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff]
    exact ⟨⟨Finset.subset_univ _, by rw [Finset.card_erase_of_mem hy.2, hy.1.2]; omega⟩,
      ⟨Finset.mem_univ _, Finset.notMem_erase _ _⟩⟩
  · rintro ⟨σ, u⟩ hx
    rw [Finset.mem_sigma, Finset.mem_sdiff] at hx
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    exact Finset.erase_insert hx.2.2
  · rintro ⟨τ, u⟩ hy
    rw [Finset.mem_sigma] at hy
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    exact Finset.insert_erase hy.2
  · rintro ⟨σ, u⟩ hx
    rw [Finset.mem_sigma, Finset.mem_sdiff] at hx
    show G σ u = G ((insert u σ).erase u) u
    rw [Finset.erase_insert hx.2.2]


omit [Fintype V] in
theorem linkRestrict_sq (f : Finset V → ℝ) (σ : Finset V) (u : V) :
    linkRestrict f σ u * linkRestrict f σ u = f (insert u σ) * f (insert u σ) := by
  rw [linkRestrict]
  have h : faceSign ℝ (insert u σ) u * faceSign ℝ (insert u σ) u = 1 := faceSign_mul_self _ _
  nlinarith [h]

omit [LinearOrder V] [Fintype V] in
/-- **The pair expansion.**  Summing `(A u + A u')²` over all ordered pairs of distinct elements of
a finite set splits into the sum of squares and the square of the sum. -/
theorem sum_pairs_sq (ρ : Finset V) (A : V → ℝ) :
    ∑ u ∈ ρ, ∑ u' ∈ ρ.erase u, (A u + A u') ^ 2
      = 2 * ((ρ.card : ℝ) - 2) * (∑ u ∈ ρ, (A u) ^ 2) + 2 * (∑ u ∈ ρ, A u) ^ 2 := by
  classical
  set S : ℝ := ∑ u ∈ ρ, A u with hS
  set Q : ℝ := ∑ u ∈ ρ, (A u) ^ 2 with hQ
  have hrow : ∀ u : V, (∑ u' ∈ ρ, (A u + A u') ^ 2)
      = (ρ.card : ℝ) * (A u) ^ 2 + 2 * A u * S + Q := by
    intro u
    rw [Finset.sum_congr rfl (fun u' (_ : u' ∈ ρ) =>
      show (A u + A u') ^ 2 = (A u) ^ 2 + 2 * A u * A u' + (A u') ^ 2 from by ring),
      Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, hS, hQ]
  have hstep : ∀ u ∈ ρ, (∑ u' ∈ ρ.erase u, (A u + A u') ^ 2)
      = (ρ.card : ℝ) * (A u) ^ 2 + 2 * A u * S + Q - 4 * (A u) ^ 2 := by
    intro u hu
    rw [Finset.sum_erase_eq_sub hu, hrow u]
    ring
  rw [Finset.sum_congr rfl hstep]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_congr rfl (fun x (_ : x ∈ ρ) => show 2 * A x * S = 2 * S * A x from by ring),
    ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, ← hS, ← hQ]
  ring


/-- The signed face value of a cochain at a vertex of a face; the coboundary is the sum of these. -/
noncomputable def coTerm (f : Finset V → ℝ) (ρ : Finset V) (w : V) : ℝ :=
  faceSign ℝ ρ w * f (ρ.erase w)

omit [Fintype V] in
theorem coTerm_sq (f : Finset V → ℝ) (ρ : Finset V) (w : V) :
    (coTerm f ρ w) ^ 2 = (f (ρ.erase w)) ^ 2 := by
  rw [coTerm, mul_pow, pow_two, faceSign_mul_self, one_mul]

omit [Fintype V] in
theorem sum_coTerm (f : Finset V → ℝ) (ρ : Finset V) :
    ∑ w ∈ ρ, coTerm f ρ w = simplicialCoboundary ℝ f ρ := rfl


omit [LinearOrder V] in
theorem sdiff_erase_erase {τ : Finset V} {v : V} (hv : v ∈ τ) :
    (univ \ (τ.erase v)).erase v = univ \ τ := by
  ext u
  simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and, not_and]
  constructor
  · rintro ⟨huv, hu⟩
    exact hu huv
  · intro hu
    exact ⟨fun hc => hu (by rw [hc]; exact hv), fun _ => hu⟩

omit [LinearOrder V] [Fintype V] in
theorem insert_insert_erase_erase {ρ : Finset V} {u v : V} (hu : u ∈ ρ) (hv : v ∈ ρ.erase u) :
    insert v (insert u ((ρ.erase u).erase v)) = ρ := by
  have hvu : v ≠ u := (Finset.mem_erase.1 hv).1
  have hvρ : v ∈ ρ := (Finset.mem_erase.1 hv).2
  rw [← Finset.erase_insert_of_ne (Ne.symm hvu), Finset.insert_erase hu, Finset.insert_erase hvρ]


namespace WeightedComplex

variable (X : WeightedComplex V)

omit [LinearOrder V] in
theorem linkGraph_mass_of_mem {σ : Finset V} {u : V} (hu : u ∈ σ) :
    (X.linkGraph σ).mass u = 0 := by
  refine Finset.sum_eq_zero fun u' _ => ?_
  rw [linkGraph_w_eq]
  exact if_pos (Or.inr (Or.inl hu))

/-- The mass norm of a cochain in degree `k`. -/
noncomputable def cochainNormSq (k : ℕ) (f : Finset V → ℝ) : ℝ :=
  ∑ τ ∈ (univ : Finset V).powersetCard (k + 1), X.m τ * (f τ * f τ)

/-- The summand of the link mass norm, as a function of the face and the vertex. -/
private noncomputable def linkTerm (n k : ℕ) (f : Finset V → ℝ) (s : Finset V) (u : V) : ℝ :=
  (((n - k : ℕ) : ℝ) * X.m (insert u s)) * (f (insert u s) * f (insert u s))

theorem link_massInner_eq {n k : ℕ} (hpure : ∀ s ∈ X.top, s.card = n + 1)
    {σ : Finset V} (hσ : σ.card = k) (f : Finset V → ℝ) :
    (X.linkGraph σ).massInner (linkRestrict f σ) (linkRestrict f σ)
      = ∑ u ∈ univ \ σ, X.linkTerm n k f σ u := by
  rw [WeightedGraph.massInner, ← Finset.sum_sdiff (Finset.subset_univ σ)]
  have hzero : ∑ u ∈ σ, (X.linkGraph σ).mass u * (linkRestrict f σ u * linkRestrict f σ u) = 0 :=
    Finset.sum_eq_zero fun u hu => by rw [X.linkGraph_mass_of_mem hu, zero_mul]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mem_sdiff] at hu
  rw [X.linkGraph_mass hpure hu.2, hσ, linkRestrict_sq, linkTerm, mul_assoc]

/-- **The link mass norms add up to the mass norm.**  Summing the mass norm of the link restriction
over all faces of dimension `k - 1` gives `(n - k)(k + 1)` times the mass norm of the cochain: the
first factor is the weighted degree in a link, the second is the number of vertices of a face. -/
theorem sum_link_massInner {n k : ℕ} (hpure : ∀ s ∈ X.top, s.card = n + 1) (f : Finset V → ℝ) :
    ∑ σ ∈ (univ : Finset V).powersetCard k,
        (X.linkGraph σ).massInner (linkRestrict f σ) (linkRestrict f σ)
      = ((n - k : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) * X.cochainNormSq k f := by
  have hstep : ∀ σ ∈ (univ : Finset V).powersetCard k,
      (X.linkGraph σ).massInner (linkRestrict f σ) (linkRestrict f σ)
        = ∑ u ∈ univ \ σ, X.linkTerm n k f σ u := by
    intro σ hσ
    rw [Finset.mem_powersetCard] at hσ
    exact X.link_massInner_eq hpure hσ.2 f
  rw [Finset.sum_congr rfl hstep, sum_powersetCard_insert, cochainNormSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  rw [Finset.mem_powersetCard] at hτ
  have hcong : ∀ u ∈ τ, X.linkTerm n k f (τ.erase u) u
      = ((n - k : ℕ) : ℝ) * X.m τ * (f τ * f τ) := by
    intro u hu
    rw [linkTerm, Finset.insert_erase hu]
  rw [Finset.sum_congr rfl hcong, Finset.sum_const, hτ.2, nsmul_eq_mul]
  ring

omit [LinearOrder V] in
/-- **The total weight of the faces one dimension above a given face.**  On a pure `n`-dimensional
complex it is `n + 1 - |τ|` times the weight of `τ`. -/
theorem sum_m_insert {n : ℕ} (hpure : ∀ s ∈ X.top, s.card = n + 1) (τ : Finset V) :
    ∑ u ∈ univ \ τ, X.m (insert u τ) = ((n + 1 - τ.card : ℕ) : ℝ) * X.m τ := by
  classical
  rw [X.m_eq_sum_ite τ, Finset.mul_sum,
    Finset.sum_congr rfl (fun u (_ : u ∈ univ \ τ) => X.m_eq_sum_ite (insert u τ)),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [← Finset.sum_filter]
  by_cases hts : τ ⊆ s
  · have hfil : (univ \ τ).filter (fun u => insert u τ ⊆ s) = s \ τ := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.insert_subset_iff]
      constructor
      · rintro ⟨hu, hus, -⟩
        exact ⟨hus, hu⟩
      · rintro ⟨hus, hu⟩
        exact ⟨hu, hus, hts⟩
    rw [hfil, Finset.sum_const, if_pos hts, Finset.card_sdiff_of_subset hts, hpure s hs,
      nsmul_eq_mul]
  · have hfil : (univ \ τ).filter (fun u => insert u τ ⊆ s) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro u hu
      rw [Finset.mem_filter, Finset.insert_subset_iff] at hu
      exact hts hu.2.2
    rw [hfil, Finset.sum_empty, if_neg hts, mul_zero]


/-- The pair term of the link Dirichlet form. -/
private noncomputable def dirTerm (f : Finset V → ℝ) (σ : Finset V) (v u : V) : ℝ :=
  (X.linkGraph σ).w v u *
    ((linkRestrict f σ v - linkRestrict f σ u) * (linkRestrict f σ v - linkRestrict f σ u))

omit [Fintype V] in
private theorem dirTerm_eq_zero_of_mem_left {f : Finset V → ℝ} {σ : Finset V} {v : V} (hv : v ∈ σ)
    (u : V) : X.dirTerm f σ v u = 0 := by
  rw [dirTerm, linkGraph_w_eq, if_pos (Or.inr (Or.inl hv)), zero_mul]

omit [Fintype V] in
private theorem dirTerm_eq_zero_of_mem_right {f : Finset V → ℝ} {σ : Finset V} {u : V}
    (hu : u ∈ σ) (v : V) : X.dirTerm f σ v u = 0 := by
  rw [dirTerm, linkGraph_w_eq, if_pos (Or.inr (Or.inr hu)), zero_mul]

omit [Fintype V] in
private theorem dirTerm_diag {f : Finset V → ℝ} (σ : Finset V) (v : V) :
    X.dirTerm f σ v v = 0 := by
  rw [dirTerm, linkGraph_w_eq, if_pos (Or.inl rfl), zero_mul]

omit [Fintype V] in
/-- **The pair term of the link Dirichlet form, in terms of the complex.** -/
theorem dirTerm_eq {f : Finset V → ℝ} {σ : Finset V} {v u : V}
    (hv : v ∉ σ) (hu : u ∉ σ) (hvu : v ≠ u) :
    X.dirTerm f σ v u
      = X.m (insert v (insert u σ)) *
        (coTerm f (insert v (insert u σ)) v + coTerm f (insert v (insert u σ)) u) ^ 2 := by
  have hw : (X.linkGraph σ).w v u = X.m (insert v (insert u σ)) := by
    rw [linkGraph_w_eq, if_neg (by tauto)]
  have hpair := coboundary_link_pair (σ := σ) hv hu hvu f
  have hce : coTerm f (insert v (insert u σ)) v + coTerm f (insert v (insert u σ)) u
      = (faceSign ℝ (insert v (insert u σ)) u * faceSign ℝ (insert v σ) v)
        * (linkRestrict f σ v - linkRestrict f σ u) := by
    rw [coTerm, coTerm, erase_insert_insert_left hv hvu, erase_insert_insert_right hu hvu]
    exact hpair
  have hcsq : (faceSign ℝ (insert v (insert u σ)) u * faceSign ℝ (insert v σ) v) ^ 2 = 1 := by
    have h1 := faceSign_mul_self (F := ℝ) (insert v (insert u σ)) u
    have h2 := faceSign_mul_self (F := ℝ) (insert v σ) v
    calc (faceSign ℝ (insert v (insert u σ)) u * faceSign ℝ (insert v σ) v) ^ 2
        = (faceSign ℝ (insert v (insert u σ)) u * faceSign ℝ (insert v (insert u σ)) u)
          * (faceSign ℝ (insert v σ) v * faceSign ℝ (insert v σ) v) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  rw [dirTerm, hw, ← pow_two, hce, mul_pow, hcsq, one_mul]


/-- **The link Dirichlet form, with its sums restricted to the link.** -/
theorem two_dirichlet_link_eq (f : Finset V → ℝ) (σ : Finset V) :
    2 * (X.linkGraph σ).dirichlet (linkRestrict f σ) (linkRestrict f σ)
      = ∑ v ∈ univ \ σ, ∑ u ∈ (univ \ σ).erase v, X.dirTerm f σ v u := by
  classical
  have hinner : ∀ v : V, ∑ u ∈ (univ \ σ).erase v, X.dirTerm f σ v u
      = ∑ u ∈ univ, X.dirTerm f σ v u := by
    intro v
    refine Finset.sum_subset (Finset.subset_univ _) fun u _ hu => ?_
    rw [Finset.mem_erase, Finset.mem_sdiff] at hu
    by_cases huv : u = v
    · rw [huv]; exact X.dirTerm_diag σ v
    · exact X.dirTerm_eq_zero_of_mem_right (by tauto) v
  rw [Finset.sum_congr rfl (fun v (_ : v ∈ univ \ σ) => hinner v)]
  have houter : ∑ v ∈ univ \ σ, ∑ u ∈ univ, X.dirTerm f σ v u
      = ∑ v ∈ univ, ∑ u ∈ univ, X.dirTerm f σ v u := by
    refine Finset.sum_subset (Finset.subset_univ _) fun v _ hv => ?_
    rw [Finset.mem_sdiff] at hv
    refine Finset.sum_eq_zero fun u _ => X.dirTerm_eq_zero_of_mem_left (by tauto) u
  rw [houter]
  show 2 * ((∑ v, ∑ u, X.dirTerm f σ v u) / 2) = ∑ v, ∑ u, X.dirTerm f σ v u
  ring


/-- **The link Dirichlet forms, reindexed over the faces two dimensions up.**  Each unordered pair
of vertices of a face of dimension `k + 1` contributes to exactly one link. -/
theorem sum_two_dirichlet_link (f : Finset V → ℝ) (k : ℕ) :
    ∑ σ ∈ (univ : Finset V).powersetCard k,
        2 * (X.linkGraph σ).dirichlet (linkRestrict f σ) (linkRestrict f σ)
      = ∑ ρ ∈ (univ : Finset V).powersetCard (k + 2),
          X.m ρ * ∑ u ∈ ρ, ∑ v ∈ ρ.erase u, (coTerm f ρ u + coTerm f ρ v) ^ 2 := by
  classical
  have h1 : ∑ σ ∈ (univ : Finset V).powersetCard k,
      2 * (X.linkGraph σ).dirichlet (linkRestrict f σ) (linkRestrict f σ)
      = ∑ σ ∈ (univ : Finset V).powersetCard k, ∑ v ∈ univ \ σ,
          ∑ u ∈ (univ \ σ).erase v, X.dirTerm f σ v u :=
    Finset.sum_congr rfl fun σ _ => X.two_dirichlet_link_eq f σ
  rw [h1, sum_powersetCard_insert k (fun σ v => ∑ u ∈ (univ \ σ).erase v, X.dirTerm f σ v u)]
  have h3 : ∀ τ ∈ (univ : Finset V).powersetCard (k + 1),
      (∑ v ∈ τ, ∑ u ∈ (univ \ (τ.erase v)).erase v, X.dirTerm f (τ.erase v) v u)
        = ∑ u ∈ univ \ τ, ∑ v ∈ τ, X.dirTerm f (τ.erase v) v u := by
    intro τ _
    rw [Finset.sum_congr rfl (fun v hv => by rw [sdiff_erase_erase hv])]
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl h3,
    sum_powersetCard_insert (k + 1) (fun τ u => ∑ v ∈ τ, X.dirTerm f (τ.erase v) v u)]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hvu : v ≠ u := (Finset.mem_erase.1 hv).1
  have hvσ : v ∉ (ρ.erase u).erase v := Finset.notMem_erase _ _
  have huσ : u ∉ (ρ.erase u).erase v := fun hc =>
    (Finset.notMem_erase u ρ) (Finset.mem_of_mem_erase hc)
  rw [X.dirTerm_eq hvσ huσ hvu, insert_insert_erase_erase hu hv]
  ring


omit [LinearOrder V] in
/-- **The total weight of a cochain over the faces two dimensions up.** -/
theorem sum_m_face_erase {n k : ℕ} (hpure : ∀ s ∈ X.top, s.card = n + 1) (f : Finset V → ℝ) :
    ∑ ρ ∈ (univ : Finset V).powersetCard (k + 2), X.m ρ * ∑ u ∈ ρ, (f (ρ.erase u)) ^ 2
      = ((n - k : ℕ) : ℝ) * X.cochainNormSq k f := by
  classical
  have h := sum_powersetCard_insert (V := V) (k + 1) (fun τ u => X.m (insert u τ) * (f τ) ^ 2)
  have hR : ∑ ρ ∈ (univ : Finset V).powersetCard (k + 2),
        ∑ u ∈ ρ, X.m (insert u (ρ.erase u)) * (f (ρ.erase u)) ^ 2
      = ∑ ρ ∈ (univ : Finset V).powersetCard (k + 2), X.m ρ * ∑ u ∈ ρ, (f (ρ.erase u)) ^ 2 := by
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u hu => by rw [Finset.insert_erase hu]
  have hL : ∑ τ ∈ (univ : Finset V).powersetCard (k + 1),
        ∑ u ∈ univ \ τ, X.m (insert u τ) * (f τ) ^ 2
      = ((n - k : ℕ) : ℝ) * X.cochainNormSq k f := by
    rw [cochainNormSq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ hτ => ?_
    rw [Finset.mem_powersetCard] at hτ
    rw [← Finset.sum_mul, X.sum_m_insert hpure τ, hτ.2,
      show n + 1 - (k + 1) = n - k from by omega]
    ring
  rw [← hR, ← h, hL]


/-- **Garland's localization identity for the Dirichlet forms.**  Summing the Dirichlet form of the
link restriction over all faces of dimension `k - 1` gives the norm of the coboundary plus
`k(n - k)` times the norm of the cochain. -/
theorem sum_link_dirichlet {n k : ℕ} (hpure : ∀ s ∈ X.top, s.card = n + 1) (f : Finset V → ℝ) :
    ∑ σ ∈ (univ : Finset V).powersetCard k,
        (X.linkGraph σ).dirichlet (linkRestrict f σ) (linkRestrict f σ)
      = X.cochainNormSq (k + 1) (simplicialCoboundary ℝ f)
        + (k : ℝ) * ((n - k : ℕ) : ℝ) * X.cochainNormSq k f := by
  classical
  have h2 : ∑ σ ∈ (univ : Finset V).powersetCard k,
      2 * (X.linkGraph σ).dirichlet (linkRestrict f σ) (linkRestrict f σ)
      = 2 * ∑ σ ∈ (univ : Finset V).powersetCard k,
        (X.linkGraph σ).dirichlet (linkRestrict f σ) (linkRestrict f σ) :=
    (Finset.mul_sum _ _ _).symm
  have hinner : ∀ ρ ∈ (univ : Finset V).powersetCard (k + 2),
      X.m ρ * ∑ u ∈ ρ, ∑ v ∈ ρ.erase u, (coTerm f ρ u + coTerm f ρ v) ^ 2
        = 2 * (k : ℝ) * (X.m ρ * ∑ u ∈ ρ, (f (ρ.erase u)) ^ 2)
          + 2 * (X.m ρ * (simplicialCoboundary ℝ f ρ * simplicialCoboundary ℝ f ρ)) := by
    intro ρ hρ
    rw [Finset.mem_powersetCard] at hρ
    rw [sum_pairs_sq ρ (coTerm f ρ), hρ.2,
      Finset.sum_congr rfl (fun w (_ : w ∈ ρ) => coTerm_sq f ρ w), sum_coTerm]
    push_cast
    ring
  have hmain := X.sum_two_dirichlet_link f k
  rw [h2, Finset.sum_congr rfl hinner, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, X.sum_m_face_erase hpure f] at hmain
  have hnorm : ∑ ρ ∈ (univ : Finset V).powersetCard (k + 2),
      X.m ρ * (simplicialCoboundary ℝ f ρ * simplicialCoboundary ℝ f ρ)
      = X.cochainNormSq (k + 1) (simplicialCoboundary ℝ f) := rfl
  rw [hnorm] at hmain
  linarith [hmain]


/-- **The codifferential**, unnormalized: the adjoint of the simplicial coboundary for the face
weights of the complex. -/
noncomputable def codiff (f : Finset V → ℝ) (τ : Finset V) : ℝ :=
  ∑ u ∈ univ \ τ, X.m (insert u τ) * (faceSign ℝ (insert u τ) u * f (insert u τ))

/-- **The mass average of a link restriction is the codifferential.** -/
theorem sum_mass_linkRestrict {n : ℕ} (hpure : ∀ s ∈ X.top, s.card = n + 1)
    (f : Finset V → ℝ) (σ : Finset V) :
    (∑ u, (X.linkGraph σ).mass u * linkRestrict f σ u)
      = ((n - σ.card : ℕ) : ℝ) * X.codiff f σ := by
  classical
  rw [codiff, Finset.mul_sum, ← Finset.sum_sdiff (Finset.subset_univ σ)]
  have hzero : ∑ u ∈ σ, (X.linkGraph σ).mass u * linkRestrict f σ u = 0 :=
    Finset.sum_eq_zero fun u hu => by rw [X.linkGraph_mass_of_mem hu, zero_mul]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mem_sdiff] at hu
  rw [X.linkGraph_mass hpure hu.2, linkRestrict]
  ring

/-- **The codifferential is adjoint to the coboundary.** -/
theorem codiff_adjoint (f g : Finset V → ℝ) (k : ℕ) :
    ∑ ρ ∈ (univ : Finset V).powersetCard (k + 2), X.m ρ * (simplicialCoboundary ℝ f ρ * g ρ)
      = ∑ τ ∈ (univ : Finset V).powersetCard (k + 1), f τ * X.codiff g τ := by
  classical
  have h := sum_powersetCard_insert (V := V) (k + 1)
    (fun τ u => X.m (insert u τ) * (faceSign ℝ (insert u τ) u * g (insert u τ)) * f τ)
  have hL : ∑ τ ∈ (univ : Finset V).powersetCard (k + 1),
      ∑ u ∈ univ \ τ, X.m (insert u τ) * (faceSign ℝ (insert u τ) u * g (insert u τ)) * f τ
      = ∑ τ ∈ (univ : Finset V).powersetCard (k + 1), f τ * X.codiff g τ := by
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [codiff, ← Finset.sum_mul]
    ring
  have hR : ∑ ρ ∈ (univ : Finset V).powersetCard (k + 2),
      ∑ u ∈ ρ, X.m (insert u (ρ.erase u)) *
        (faceSign ℝ (insert u (ρ.erase u)) u * g (insert u (ρ.erase u))) * f (ρ.erase u)
      = ∑ ρ ∈ (univ : Finset V).powersetCard (k + 2),
        X.m ρ * (simplicialCoboundary ℝ f ρ * g ρ) := by
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [simplicialCoboundary_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.insert_erase hu]
    ring
  rw [← hL, h, hR]


omit [LinearOrder V] in
theorem cochainNormSq_nonneg (k : ℕ) (f : Finset V → ℝ) : 0 ≤ X.cochainNormSq k f :=
  Finset.sum_nonneg fun τ _ => mul_nonneg (X.m_nonneg τ) (mul_self_nonneg _)

/-- **Garland's vanishing, analytic core.**  A cocycle whose link restrictions all have mass
average zero is zero, as soon as every link of a `k`-face has a spectral gap larger than
`k / (k + 1)`.  The two localization identities turn the spectral gap into the inequality
`k ≥ lam (k + 1)` on a nonzero cochain, which the hypothesis forbids. -/
theorem cochainNormSq_eq_zero_of_spectralGap {n k : ℕ} (hpure : ∀ s ∈ X.top, s.card = n + 1)
    (hkn : k < n) (f : Finset V → ℝ) (lam : ℝ)
    (hgap : ∀ σ ∈ (univ : Finset V).powersetCard k, (X.linkGraph σ).HasSpectralGap lam)
    (hmean : ∀ σ ∈ (univ : Finset V).powersetCard k,
      (∑ u, (X.linkGraph σ).mass u * linkRestrict f σ u) = 0)
    (hclosed : simplicialCoboundary ℝ f = 0)
    (hlam : (k : ℝ) < lam * ((k : ℝ) + 1)) :
    X.cochainNormSq k f = 0 := by
  classical
  have hD := X.sum_link_dirichlet hpure f (k := k)
  have hM := X.sum_link_massInner hpure f (k := k)
  have hzero : X.cochainNormSq (k + 1) (simplicialCoboundary ℝ f) = 0 := by
    refine Finset.sum_eq_zero fun ρ _ => ?_
    rw [hclosed]
    simp
  have hge : ∀ σ ∈ (univ : Finset V).powersetCard k,
      lam * (X.linkGraph σ).massInner (linkRestrict f σ) (linkRestrict f σ)
        ≤ (X.linkGraph σ).dirichlet (linkRestrict f σ) (linkRestrict f σ) :=
    fun σ hσ => hgap σ hσ (linkRestrict f σ) (hmean σ hσ)
  have hsum : lam * ∑ σ ∈ (univ : Finset V).powersetCard k,
        (X.linkGraph σ).massInner (linkRestrict f σ) (linkRestrict f σ)
      ≤ ∑ σ ∈ (univ : Finset V).powersetCard k,
        (X.linkGraph σ).dirichlet (linkRestrict f σ) (linkRestrict f σ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hge
  rw [hM, hD, hzero, zero_add] at hsum
  have hN : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hkn
  have hP : 0 ≤ X.cochainNormSq k f := X.cochainNormSq_nonneg k f
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hsum
  by_contra hne
  have hPpos : 0 < X.cochainNormSq k f := lt_of_le_of_ne hP (Ne.symm hne)
  nlinarith [hsum, mul_pos (sub_pos.2 hlam) (mul_pos hN hPpos)]


omit [LinearOrder V] in
theorem eq_zero_of_cochainNormSq_eq_zero {k : ℕ} {f : Finset V → ℝ}
    (h : X.cochainNormSq k f = 0) {τ : Finset V} (hτ : τ.card = k + 1) (hm : X.m τ ≠ 0) :
    f τ = 0 := by
  have hmem : τ ∈ (univ : Finset V).powersetCard (k + 1) :=
    Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hτ⟩
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun σ (_ : σ ∈ (univ : Finset V).powersetCard (k + 1)) =>
      mul_nonneg (X.m_nonneg σ) (mul_self_nonneg _))).1 h τ hmem
  rcases mul_eq_zero.1 hterm with h1 | h2
  · exact absurd h1 hm
  · exact mul_self_eq_zero.1 h2

/-- **Garland's vanishing theorem.**  On a pure `n`-dimensional weighted complex whose links of
`k`-faces all have a spectral gap larger than `k / (k + 1)`, every harmonic `k`-cochain vanishes on
every face of positive weight. -/
theorem harmonic_eq_zero {n k : ℕ} (hpure : ∀ s ∈ X.top, s.card = n + 1) (hkn : k < n)
    (f : Finset V → ℝ) (lam : ℝ)
    (hgap : ∀ σ ∈ (univ : Finset V).powersetCard k, (X.linkGraph σ).HasSpectralGap lam)
    (hclosed : simplicialCoboundary ℝ f = 0) (hcoclosed : ∀ σ, X.codiff f σ = 0)
    (hlam : (k : ℝ) < lam * ((k : ℝ) + 1))
    {τ : Finset V} (hτ : τ.card = k + 1) (hm : X.m τ ≠ 0) :
    f τ = 0 :=
  X.eq_zero_of_cochainNormSq_eq_zero
    (X.cochainNormSq_eq_zero_of_spectralGap hpure hkn f lam hgap
      (fun σ _ => by rw [X.sum_mass_linkRestrict hpure f σ, hcoclosed σ, mul_zero]) hclosed hlam)
    hτ hm


end WeightedComplex

end GaloisForLFunctions.HTGeometry
