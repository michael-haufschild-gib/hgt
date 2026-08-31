import GaloisForLFunctions.HTGeometry.RittAffineRigidity
import GaloisForLFunctions.HTGeometry.RittHomogeneousTowerDescent

/-!
# One level of the jet-tower descent, with the denominator removed

Applying the affine dichotomy in the tower's top coordinate.  An eigen-inhomogeneous relation over
the first `m + 1` jets leaves exactly one of five situations at level `m`:

* the linear coefficient of the inhomogeneity vanishes and `W` is already over the first `m` jets —
  the relation is unchanged, in particular its scalar is unchanged;
* the `m`-th jet has no shift defect at all;
* the affine connection of the `m`-th coordinate has a nonzero solution;
* a homogeneous relation with scalar `c·(q/ρ^m)^{−D}`, `D ≥ 2`;
* an affine relation with scalar `c·(q/ρ^m)^{−1}` and constant inhomogeneity.

The exponent by which the scalar is divided is the degree of the *numerator* of the coprime
representation, never a difference of degrees, so it is never negative.  That is the property the
old slice lacked and the reason the accumulated exponents of a descent can no longer cancel.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [Field L] [CharZero L] [Algebra K L]

/-- **One level of the affine descent, in five exclusive shapes.**  The constant part of the
inhomogeneity is an arbitrary element of the lower prefix field. -/
theorem affine_descent_dichotomy_gen (Fr : RittFrame K L) {τ : L} {q : K}
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    {m : ℕ} (htr : Transcendental ↥(Fr.jetPrefixField τ m) (Fr.d^[m] τ))
    {W : L} (hW0 : W ≠ 0) (hWmem : W ∈ Fr.jetPrefixField τ (m + 1))
    {c α : K} (hc : c ≠ 0) {β : L} (hβmem : β ∈ Fr.jetPrefixField τ m)
    (hrel : Fr.σ W = algebraMap K L c * W + (algebraMap K L α * Fr.d^[m] τ + β)) :
    (α = 0 ∧ W ∈ Fr.jetPrefixField τ m) ∨
    (Fr.σ (Fr.d^[m] τ) = algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ) ∨
    (∃ (w : L) (N : ℕ) (A' : ℕ → K), w ≠ 0 ∧ w ∈ Fr.jetPrefixField τ m ∧ 1 ≤ N ∧
      (Fr.σ (Fr.d^[m] τ) = algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ
        + ∑ j ∈ Finset.range m, algebraMap K L (A' j) * Fr.d^[j] τ) ∧
      Fr.σ w = algebraMap K L (q / Fr.ρ ^ m) * w
        + ∑ j ∈ Finset.range m, algebraMap K L (-(N : K) * A' j) * Fr.d^[j] τ) ∨
    (∃ v z y : L, v ≠ 0 ∧ v ∈ Fr.jetPrefixField τ m ∧ z ∈ Fr.jetPrefixField τ m ∧
      y ∈ Fr.jetPrefixField τ m ∧ α ≠ 0 ∧
      Fr.σ v = algebraMap K L (c / (q / Fr.ρ ^ m) ^ 2) * v ∧
      Fr.σ z = algebraMap K L (q / Fr.ρ ^ m) * z
        + algebraMap K L ((q / Fr.ρ ^ m) * α / c) / v
        - (2 : L) * (Fr.σ (Fr.d^[m] τ)
            - algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ) ∧
      Fr.σ y = algebraMap K L ((q / Fr.ρ ^ m) ^ 2) * y
        - algebraMap K L (q / Fr.ρ ^ m)
            * (Fr.σ (Fr.d^[m] τ) - algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ) * z
        + (Fr.σ (Fr.d^[m] τ) - algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ) ^ 2
        + algebraMap K L (q / Fr.ρ ^ m)
            * (algebraMap K L (q / Fr.ρ ^ m) * β - algebraMap K L α
                * (Fr.σ (Fr.d^[m] τ) - algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ))
          / (algebraMap K L c * v)) ∨
    (∃ v : L, v ≠ 0 ∧ v ∈ Fr.jetPrefixField τ m ∧
      Fr.σ v = algebraMap K L (c / (q / Fr.ρ ^ m)) * v
        + algebraMap K L (α / (q / Fr.ρ ^ m)) ∧
      (α = 0 → ∃ y : L, y ∈ Fr.jetPrefixField τ m ∧
        Fr.σ y = algebraMap K L (q / Fr.ρ ^ m) * y
          + algebraMap K L (q / Fr.ρ ^ m) * β / (algebraMap K L c * v)
          - (Fr.σ (Fr.d^[m] τ)
              - algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ))) := by
  classical
  set E : IntermediateField K L := Fr.jetPrefixField τ m with hE
  have hEσ : ∀ x ∈ E, Fr.σ x ∈ E := Fr.sigma_mem_jetPrefixField hqconst hshift m
  set φ : ↥E →+* ↥E :=
    { toFun := fun x => ⟨Fr.σ (x : L), hEσ (x : L) x.2⟩
      map_one' := by ext; simp
      map_mul' := fun _ _ => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp } with hφ
  have hcompE : ∀ x : ↥E, Fr.σ (algebraMap ↥E L x) = algebraMap ↥E L (φ x) := fun _ => rfl
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  set aK : K := q / Fr.ρ ^ m with haK
  have haK0 : aK ≠ 0 := div_ne_zero hq (pow_ne_zero _ hρ0)
  have haKL : algebraMap K L aK ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr haK0
  set aE : ↥E := ⟨algebraMap K L aK, IntermediateField.algebraMap_mem _ _⟩ with haE
  have haE0 : aE ≠ 0 := by
    intro h
    exact ((map_ne_zero_iff _ (algebraMap K L).injective).mpr haK0) (congrArg Subtype.val h)
  obtain ⟨A₀, hA₀supp, hA₀⟩ := exists_shift_jet_coeffs Fr hshift m
  set v : L := ∑ j ∈ Finset.range m, algebraMap K L (A₀ j) * Fr.d^[j] τ with hv
  have hvE : v ∈ E := by
    refine sum_mem ?_
    intro j hj
    rw [Finset.mem_range] at hj
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (Fr.jet_mem_jetPrefixField hj)
  set bE : ↥E := ⟨v, hvE⟩ with hbE
  have hσt : Fr.σ (Fr.d^[m] τ)
      = algebraMap ↥E L aE * Fr.d^[m] τ + algebraMap ↥E L bE := by
    show Fr.σ (Fr.d^[m] τ) = algebraMap K L aK * Fr.d^[m] τ + v
    rw [hv]
    exact hA₀
  set cE : ↥E := ⟨algebraMap K L c, IntermediateField.algebraMap_mem _ _⟩ with hcE
  have hcE0 : cE ≠ 0 := by
    intro h
    exact ((map_ne_zero_iff _ (algebraMap K L).injective).mpr hc) (congrArg Subtype.val h)
  set αE : ↥E := ⟨algebraMap K L α, IntermediateField.algebraMap_mem _ _⟩ with hαE
  set βE : ↥E := ⟨β, hβmem⟩ with hβE
  have hrelE : Fr.σ W = algebraMap ↥E L cE * W
      + (algebraMap ↥E L αE * Fr.d^[m] τ + algebraMap ↥E L βE) := hrel
  have hWmem' : W ∈ IntermediateField.adjoin ↥E ({Fr.d^[m] τ} : Set L) := by
    have := (jetPrefixField_succ_eq Fr τ m) ▸ hWmem
    exact this
  have hres := affine_eigen_dichotomy (E := ↥E) Fr.σ φ hcompE htr haE0 hcE0 hσt hW0 hWmem' hrelE
  rcases hres with h1 | h2 | h3 | h4 | h5
  · obtain ⟨hα0, x, hx⟩ := h1
    refine Or.inl ⟨?_, ?_⟩
    · have h := congrArg (fun z : ↥E => (z : L)) hα0
      simp only [hαE] at h
      refine (algebraMap K L).injective ?_
      rw [map_zero]
      simpa using h
    · rw [hx]; exact x.2
  · refine Or.inr (Or.inl ?_)
    have hbv : v = 0 := h2
    rw [hA₀, hbv, add_zero]
  · obtain ⟨w, N, hw0, hN, hconn⟩ := h3
    refine Or.inr (Or.inr (Or.inl ⟨(w : L), N, A₀, ?_, w.2, hN, hA₀, ?_⟩))
    · intro h
      exact hw0 (Subtype.ext (by simpa using h))
    · have hcast := congrArg (fun z : ↥E => (z : L)) hconn
      simp only [hφ, haE, hbE] at hcast
      push_cast at hcast
      have hsum : ∑ j ∈ Finset.range m, algebraMap K L (-(N : K) * A₀ j) * Fr.d^[j] τ
          = -((N : L) * v) := by
        rw [hv, Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, map_neg, map_natCast]
        ring
      rw [hsum]
      linear_combination hcast
  · obtain ⟨u, Z, Y, hu0, hαne, heq, hratio, hconst⟩ := h4
    have hAm : α ≠ 0 := by
      intro h
      refine hαne (Subtype.ext ?_)
      show algebraMap K L α = ((0 : ↥E) : L)
      rw [h, map_zero]
      rfl
    have huL : (u : L) ≠ 0 := fun h => hu0 (Subtype.ext (by simpa using h))
    have hbval : ((bE : ↥E) : L)
        = Fr.σ (Fr.d^[m] τ) - algebraMap K L aK * Fr.d^[m] τ := by
      have h : Fr.σ (Fr.d^[m] τ) = algebraMap K L aK * Fr.d^[m] τ + ((bE : ↥E) : L) := hσt
      linear_combination -h
    refine Or.inr (Or.inr (Or.inr (Or.inl
      ⟨(u : L), (Z : L), (Y : L), huL, u.2, Z.2, Y.2, hAm, ?_, ?_, ?_⟩)))
    · have hcast := congrArg (fun z : ↥E => (z : L)) heq
      simp only [hφ, haE, hcE] at hcast
      push_cast at hcast
      have e1 : algebraMap K L (c / aK ^ 2) = algebraMap K L c / algebraMap K L aK ^ 2 := by
        rw [map_div₀, map_pow]
      rw [e1, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 haKL)]
      linear_combination hcast
    · have hcast := congrArg (fun z : ↥E => (z : L)) hratio
      simp only [hφ, haE, hcE, hαE] at hcast
      push_cast at hcast
      rw [show ((2 : ↥E) : L) = (2 : L) from map_ofNat (algebraMap ↥E L) 2] at hcast
      have e2 : algebraMap K L (aK * α / c)
          = algebraMap K L aK * algebraMap K L α / algebraMap K L c := by
        rw [map_div₀, map_mul]
      rw [e2, ← hbval]
      linear_combination hcast
    · have hcast := congrArg (fun z : ↥E => (z : L)) hconst
      simp only [hφ, haE, hcE, hαE, hβE] at hcast
      push_cast at hcast
      have e3 : algebraMap K L (aK ^ 2) = algebraMap K L aK ^ 2 := map_pow _ _ _
      rw [e3, ← hbval]
      linear_combination hcast
  · obtain ⟨u, hu⟩ := h5
    have hu0 := hu.1
    have heq := hu.2.1
    have hlin := hu.2.2
    have hbval : ((bE : ↥E) : L)
        = Fr.σ (Fr.d^[m] τ) - algebraMap K L aK * Fr.d^[m] τ := by
      have h : Fr.σ (Fr.d^[m] τ) = algebraMap K L aK * Fr.d^[m] τ + ((bE : ↥E) : L) := hσt
      linear_combination -h
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨(u : L), ?_, u.2, ?_, ?_⟩)))
    · intro h
      exact hu0 (Subtype.ext (by simpa using h))
    · have hcast := congrArg (fun z : ↥E => (z : L)) heq
      simp only [hφ, haE, hcE, hαE] at hcast
      push_cast at hcast
      have e1 : algebraMap K L (c / aK) = algebraMap K L c / algebraMap K L aK :=
        map_div₀ _ _ _
      have e2 : algebraMap K L (α / aK) = algebraMap K L α / algebraMap K L aK :=
        map_div₀ _ _ _
      rw [e1, e2, div_mul_eq_mul_div, ← add_div, eq_div_iff haKL]
      linear_combination hcast
    · intro hα0
      have hαE0 : αE = 0 := by
        refine Subtype.ext ?_
        show algebraMap K L α = ((0 : ↥E) : L)
        rw [hα0, map_zero]
        rfl
      obtain ⟨Y, hY⟩ := hlin hαE0
      refine ⟨(Y : L), Y.2, ?_⟩
      have hcast := congrArg (fun z : ↥E => (z : L)) hY
      simp only [hφ, haE, hcE, hβE] at hcast
      push_cast at hcast
      rw [← hbval]
      linear_combination hcast

/-- **One level of the affine descent**, for an inhomogeneity that is a base-linear combination of
the jets. -/
theorem affine_descent_dichotomy (Fr : RittFrame K L) {τ : L} {q : K}
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    {m : ℕ} (htr : Transcendental ↥(Fr.jetPrefixField τ m) (Fr.d^[m] τ))
    {W : L} (hW0 : W ≠ 0) (hWmem : W ∈ Fr.jetPrefixField τ (m + 1))
    {c g : K} (hc : c ≠ 0) {A : ℕ → K}
    (hrel : Fr.σ W = algebraMap K L c * W + algebraMap K L g
      + ∑ j ∈ Finset.range (m + 1), algebraMap K L (A j) * Fr.d^[j] τ) :
    (A m = 0 ∧ W ∈ Fr.jetPrefixField τ m) ∨
    (Fr.σ (Fr.d^[m] τ) = algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ) ∨
    (∃ (w : L) (N : ℕ) (A' : ℕ → K), w ≠ 0 ∧ w ∈ Fr.jetPrefixField τ m ∧ 1 ≤ N ∧
      (Fr.σ (Fr.d^[m] τ) = algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ
        + ∑ j ∈ Finset.range m, algebraMap K L (A' j) * Fr.d^[j] τ) ∧
      Fr.σ w = algebraMap K L (q / Fr.ρ ^ m) * w
        + ∑ j ∈ Finset.range m, algebraMap K L (-(N : K) * A' j) * Fr.d^[j] τ) ∨
    (∃ v z y : L, v ≠ 0 ∧ v ∈ Fr.jetPrefixField τ m ∧ z ∈ Fr.jetPrefixField τ m ∧
      y ∈ Fr.jetPrefixField τ m ∧ A m ≠ 0 ∧
      Fr.σ v = algebraMap K L (c / (q / Fr.ρ ^ m) ^ 2) * v ∧
      Fr.σ z = algebraMap K L (q / Fr.ρ ^ m) * z
        + algebraMap K L ((q / Fr.ρ ^ m) * A m / c) / v
        - (2 : L) * (Fr.σ (Fr.d^[m] τ)
            - algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ) ∧
      Fr.σ y = algebraMap K L ((q / Fr.ρ ^ m) ^ 2) * y
        - algebraMap K L (q / Fr.ρ ^ m)
            * (Fr.σ (Fr.d^[m] τ) - algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ) * z
        + (Fr.σ (Fr.d^[m] τ) - algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ) ^ 2
        + algebraMap K L (q / Fr.ρ ^ m)
            * (algebraMap K L (q / Fr.ρ ^ m)
                  * (algebraMap K L g + ∑ j ∈ Finset.range m,
                      algebraMap K L (A j) * Fr.d^[j] τ)
              - algebraMap K L (A m)
                * (Fr.σ (Fr.d^[m] τ) - algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ))
          / (algebraMap K L c * v)) ∨
    (∃ v : L, v ≠ 0 ∧ v ∈ Fr.jetPrefixField τ m ∧
      Fr.σ v = algebraMap K L (c / (q / Fr.ρ ^ m)) * v
        + algebraMap K L (A m / (q / Fr.ρ ^ m)) ∧
      (A m = 0 → ∃ y : L, y ∈ Fr.jetPrefixField τ m ∧
        Fr.σ y = algebraMap K L (q / Fr.ρ ^ m) * y
          + algebraMap K L (q / Fr.ρ ^ m)
              * (algebraMap K L g + ∑ j ∈ Finset.range m, algebraMap K L (A j) * Fr.d^[j] τ)
              / (algebraMap K L c * v)
          - (Fr.σ (Fr.d^[m] τ)
              - algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ))) := by
  have hβmem : algebraMap K L g + ∑ j ∈ Finset.range m, algebraMap K L (A j) * Fr.d^[j] τ
      ∈ Fr.jetPrefixField τ m := by
    refine add_mem (IntermediateField.algebraMap_mem _ _) (sum_mem ?_)
    intro j hj
    rw [Finset.mem_range] at hj
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (Fr.jet_mem_jetPrefixField hj)
  refine affine_descent_dichotomy_gen Fr hqconst hshift hq htr hW0 hWmem hc (α := A m) hβmem ?_
  have hsplit : ∑ j ∈ Finset.range (m + 1), algebraMap K L (A j) * Fr.d^[j] τ
      = algebraMap K L (A m) * Fr.d^[m] τ
        + ∑ j ∈ Finset.range m, algebraMap K L (A j) * Fr.d^[j] τ := by
    rw [Finset.sum_range_succ]
    ring
  rw [hrel, hsplit]
  ring

end GaloisForLFunctions.HTGeometry
