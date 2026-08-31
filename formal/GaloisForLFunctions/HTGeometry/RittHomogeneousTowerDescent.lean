import GaloisForLFunctions.HTGeometry.RittHomogeneousRigidity
import GaloisForLFunctions.HTGeometry.RittTowerDescentStep

/-!
# A homogeneous relation descends the jet tower without changing its scalar

The affine slice of the tower descent multiplies the scalar of a relation by a power of the
coordinate's multiplier at every level, so nothing prevents the accumulated exponents from
cancelling.  For a *purely homogeneous* relation that freedom disappears: rigidity over an affinely
moved generator says a homogeneous eigenvector is either already in the coefficient field or produces
the affine connection of the coordinate.

Iterating, a homogeneous relation `σ W = c·W` anywhere in the jet tower yields either

* a base solution of the **same** relation, `ψ(u) = c·u` with `u ≠ 0` — no exponent drift at all; or
* an inhomogeneous relation `σ w = (q/ρ^m)·w − N·b_m` at some level `m` of the tower, with `N ≥ 1`
  and `b_m` the shift defect of the `m`-th jet.

The first alternative hands Ritt's order-one form straight back whenever the original scalar is a
nontrivial monomial in the multiplier and the chain-rule factor; the second is an affine transport
equation whose scalar is `q/ρ^m`, whose multiplier exponent is `1` and therefore never trivial.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [Field L] [CharZero L] [Algebra K L]

/-- **One level of homogeneous descent.**  A homogeneous eigenvector over the first `m + 1` jets is
either already over the first `m`, or produces the affine connection of the `m`-th coordinate. -/
theorem mem_prefix_or_affine_connection_of_eigen (Fr : RittFrame K L) {τ : L} {q : K}
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ)
    (hq : q ≠ 0) {m : ℕ} (htr : Transcendental ↥(Fr.jetPrefixField τ m) (Fr.d^[m] τ))
    {W : L} (hW0 : W ≠ 0) (hWmem : W ∈ Fr.jetPrefixField τ (m + 1))
    {c : K} (hc : c ≠ 0) (hrel : Fr.σ W = algebraMap K L c * W) :
    W ∈ Fr.jetPrefixField τ m ∨
      (Fr.σ (Fr.d^[m] τ) = algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ) ∨
      ∃ (w : L) (N : ℕ) (A : ℕ → K), w ≠ 0 ∧ w ∈ Fr.jetPrefixField τ m ∧ 1 ≤ N ∧
        (Fr.σ (Fr.d^[m] τ) = algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ
          + ∑ j ∈ Finset.range m, algebraMap K L (A j) * Fr.d^[j] τ) ∧
        Fr.σ w = algebraMap K L (q / Fr.ρ ^ m) * w
          + ∑ j ∈ Finset.range m, algebraMap K L (-(N : K) * A j) * Fr.d^[j] τ := by
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
  set aE : ↥E := ⟨algebraMap K L aK, IntermediateField.algebraMap_mem _ _⟩ with haE
  have haE0 : aE ≠ 0 := by
    intro h
    exact ((map_ne_zero_iff _ (algebraMap K L).injective).mpr haK0) (congrArg Subtype.val h)
  obtain ⟨A, hAsupp, hA⟩ := exists_shift_jet_coeffs Fr hshift m
  set v : L := ∑ j ∈ Finset.range m, algebraMap K L (A j) * Fr.d^[j] τ with hv
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
    exact hA
  set cE : ↥E := ⟨algebraMap K L c, IntermediateField.algebraMap_mem _ _⟩ with hcE
  have hcE0 : cE ≠ 0 := by
    intro h
    exact ((map_ne_zero_iff _ (algebraMap K L).injective).mpr hc) (congrArg Subtype.val h)
  have hrelE : Fr.σ W = algebraMap ↥E L cE * W := hrel
  have hWmem' : W ∈ IntermediateField.adjoin ↥E ({Fr.d^[m] τ} : Set L) := by
    have := (jetPrefixField_succ_eq Fr τ m) ▸ hWmem
    exact this
  have hres := mem_range_or_affine_connection_of_homogeneous_eigen (E := ↥E) Fr.σ φ hcompE htr
    haE0 hcE0 hσt hW0 hWmem' hrelE
  rcases hres with hcase | hb0 | hcase
  · obtain ⟨x, hx⟩ := hcase
    left
    rw [hx]
    exact x.2
  · refine Or.inr (Or.inl ?_)
    have hbv : v = 0 := hb0
    rw [hA, hbv, add_zero]
  · obtain ⟨w, N, hw0, hN, hconn⟩ := hcase
    refine Or.inr (Or.inr ⟨(w : L), N, A, ?_, w.2, hN, hA, ?_⟩)
    · intro h
      exact hw0 (Subtype.ext (by simpa using h))
    have hcast := congrArg (fun z : ↥E => (z : L)) hconn
    simp only [hφ, haE, hbE] at hcast
    push_cast at hcast
    have hsum : ∑ j ∈ Finset.range m, algebraMap K L (-(N : K) * A j) * Fr.d^[j] τ
        = -((N : L) * v) := by
      rw [hv, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_neg, map_natCast]
      ring
    rw [hsum]
    linear_combination hcast

/-- **The homogeneous tower descent.**  A homogeneous relation over the whole jet prefix field either
descends to the base with its scalar untouched, or produces the affine connection of one of the
coordinates. -/
theorem exists_base_eigen_or_affine_connection_of_tower (Fr : RittFrame K L) {τ : L} {q : K}
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0) :
    ∀ (n : ℕ), (∀ k, k < n → Transcendental ↥(Fr.jetPrefixField τ k) (Fr.d^[k] τ)) →
      ∀ (W : L) (c : K), W ≠ 0 → W ∈ Fr.jetPrefixField τ n → c ≠ 0 →
        Fr.σ W = algebraMap K L c * W →
        (∃ u : K, u ≠ 0 ∧ Fr.ψ u = c * u) ∨
        (∃ m : ℕ, m < n ∧
          Fr.σ (Fr.d^[m] τ) = algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ) ∨
        (∃ (m : ℕ) (w : L) (N : ℕ) (A : ℕ → K), m < n ∧ w ≠ 0 ∧
          w ∈ Fr.jetPrefixField τ m ∧ 1 ≤ N ∧
          (Fr.σ (Fr.d^[m] τ) = algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ
            + ∑ j ∈ Finset.range m, algebraMap K L (A j) * Fr.d^[j] τ) ∧
          Fr.σ w = algebraMap K L (q / Fr.ρ ^ m) * w
            + ∑ j ∈ Finset.range m, algebraMap K L (-(N : K) * A j) * Fr.d^[j] τ) := by
  intro n
  induction n with
  | zero =>
      intro _ W c hW0 hWmem hc hrel
      have hbot : Fr.jetPrefixField τ 0 = (⊥ : IntermediateField K L) := by
        rw [RittFrame.jetPrefixField,
          show {x : L | ∃ j < 0, x = Fr.d^[j] τ} = (∅ : Set L) by ext x; simp]
        exact IntermediateField.adjoin_empty K L
      rw [hbot, IntermediateField.mem_bot] at hWmem
      obtain ⟨u, hu⟩ := hWmem
      refine Or.inl ⟨u, ?_, ?_⟩
      · intro h
        exact hW0 (by rw [← hu, h, map_zero])
      · refine (algebraMap K L).injective ?_
        rw [map_mul, ← Fr.comp, hu]
        exact hrel
  | succ m ih =>
      intro htr W c hW0 hWmem hc hrel
      rcases mem_prefix_or_affine_connection_of_eigen Fr hqconst hshift hq (htr m (by omega))
          hW0 hWmem hc hrel with hmem | hdiag | ⟨w, N, A, hw0, hwmem, hN, hAshift, hconn⟩
      · rcases ih (fun k hk => htr k (by omega)) W c hW0 hmem hc hrel with hbase | hdg |
            ⟨m', w, N, A, hm', hw0, hwmem, hN, hAshift, hconn⟩
        · exact Or.inl hbase
        · obtain ⟨m', hm', hd⟩ := hdg
          exact Or.inr (Or.inl ⟨m', by omega, hd⟩)
        · exact Or.inr (Or.inr ⟨m', w, N, A, by omega, hw0, hwmem, hN, hAshift, hconn⟩)
      · exact Or.inr (Or.inl ⟨m, by omega, hdiag⟩)
      · exact Or.inr (Or.inr ⟨m, w, N, A, by omega, hw0, hwmem, hN, hAshift, hconn⟩)

/-- **The homogeneous tower descent, stopped at a floor.**  A homogeneous relation descends to the
floor with its scalar untouched, unless a jet at or above the floor has no shift defect or a
coordinate carries the affine connection. -/
theorem exists_floor_eigen_or_affine_connection_of_tower (Fr : RittFrame K L) {τ : L} {q : K}
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0) (F : ℕ) :
    ∀ (n : ℕ), (∀ k, k < n → Transcendental ↥(Fr.jetPrefixField τ k) (Fr.d^[k] τ)) →
      ∀ (W : L) (c : K), W ≠ 0 → W ∈ Fr.jetPrefixField τ n → c ≠ 0 →
        Fr.σ W = algebraMap K L c * W →
        (∃ n' : ℕ, n' ≤ F ∧ n' ≤ n ∧ W ∈ Fr.jetPrefixField τ n') ∨
        (∃ m : ℕ, F ≤ m ∧ m < n ∧
          Fr.σ (Fr.d^[m] τ) = algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ) ∨
        (∃ (m : ℕ) (w : L) (N : ℕ) (A : ℕ → K), F ≤ m ∧ m < n ∧ w ≠ 0 ∧
          w ∈ Fr.jetPrefixField τ m ∧ 1 ≤ N ∧
          (Fr.σ (Fr.d^[m] τ) = algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ
            + ∑ j ∈ Finset.range m, algebraMap K L (A j) * Fr.d^[j] τ) ∧
          Fr.σ w = algebraMap K L (q / Fr.ρ ^ m) * w
            + ∑ j ∈ Finset.range m, algebraMap K L (-(N : K) * A j) * Fr.d^[j] τ) := by
  intro n
  induction n with
  | zero =>
      intro _ W c hW0 hWmem hc hrel
      exact Or.inl ⟨0, Nat.zero_le _, le_rfl, hWmem⟩
  | succ m ih =>
      intro htr W c hW0 hWmem hc hrel
      by_cases hFloor : m + 1 ≤ F
      · exact Or.inl ⟨m + 1, hFloor, le_rfl, hWmem⟩
      have hFm : F ≤ m := by omega
      rcases mem_prefix_or_affine_connection_of_eigen Fr hqconst hshift hq (htr m (by omega))
          hW0 hWmem hc hrel with hmem | hdiag | ⟨w, N, A, hw0, hwmem, hN, hAshift, hconn⟩
      · rcases ih (fun k hk => htr k (by omega)) W c hW0 hmem hc hrel with
            ⟨n', hn'F, hn'm, hVmem⟩ | ⟨m', hFm', hm', hd⟩ |
            ⟨m', w, N, A, hFm', hm', hw0, hwmem, hN, hAshift, hconn⟩
        · exact Or.inl ⟨n', hn'F, by omega, hVmem⟩
        · exact Or.inr (Or.inl ⟨m', hFm', by omega, hd⟩)
        · exact Or.inr (Or.inr ⟨m', w, N, A, hFm', by omega, hw0, hwmem, hN, hAshift, hconn⟩)
      · exact Or.inr (Or.inl ⟨m, hFm, by omega, hdiag⟩)
      · exact Or.inr (Or.inr ⟨m, w, N, A, hFm, by omega, hw0, hwmem, hN, hAshift, hconn⟩)

end GaloisForLFunctions.HTGeometry
