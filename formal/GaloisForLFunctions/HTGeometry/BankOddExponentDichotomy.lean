import GaloisForLFunctions.HTGeometry.MeromorphicGammaComplexScale
import GaloisForLFunctions.HTGeometry.TranslationStableDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.SourceLogarithmicBoundary

/-!
# Bank's theorem: the odd-exponent canonical product is hypertranscendental

For a primitive `p`-th root of unity `ω` the ray product `∏_{j<p} Γ(ω^j z + 1)⁻¹` has logarithmic
derivative `−Φ` with

`Φ = ∑_{j<p} ψ(ω^j z + 1) · ω^j`,

a sum of digamma elements at the `p` pairwise distinct scales `ω^j`.  Each scale `a` owns one
translation step that is *integral* for it, namely `a⁻¹`: translating by `a⁻¹` raises the parameter
of `Γ(a z + b)` by one, so the alternating subset sum of translations over a family containing that
step is rational.

Apply the difference operator obtained from the steps `τ_k = ω^{−k}` with `k` ranging over
`{1,…,p−1}` — the index `k = 0` is *omitted*.  For every `j ≠ 0` the step `k = j` belongs to the
family and is integral for the scale `ω^j`, so that whole component is rational.  For `j = 0` no step
of the family is integral for the scale `1`, and what survives is a pure common-scale combination

`A = ∑_{S ⊆ {1,…,p−1}} (−1)^{|S|} ψ(z + 1 + σ_S)`,  `σ_S = ∑_{k∈S} ω^{−k}`.

The shift orbits of the parameters `1 + σ_S` are separated by the imaginary part: it is a `ℤ`-linear
functional annihilating `ℤ`, and for odd `p` no step `ω^{−k}` with `1 ≤ k < p` is real, so among the
`2^{p−1}` subset sums the imaginary part is strictly maximised by the subset on which the steps have
positive imaginary part, and by that subset alone.  Every charge `(−1)^{|S|}` is nonzero, so the
separated-orbit Gamma law makes `A` hypertranscendental, contradicting its differential algebraicity.
Hence `Φ`, hence the ray product, hence the canonical product `W_p` with zeros `−n^p`, is
hypertranscendental for every odd `p ≥ 3`; together with the even case this is Bank's dichotomy.
-/

namespace HTGeometry

open GaloisForLFunctions GaloisForLFunctions.HTGeometry Bottcher

noncomputable section

open scoped UnivMeroFieldInstances

/-! ## Parameter translation and the scale one -/

/-- **Parameter translation of the scaled digamma.**  Translating the coordinate by `h` moves the
shift parameter of `ψ(a z + b)` by `a h`. -/
theorem addTranslationMeroEquiv_digammaScaleShiftMero_param (a : ℂ) (ha : a ≠ 0) (h b : ℂ) :
    addTranslationMeroEquiv h (digammaScaleShiftMero a ha b)
      = digammaScaleShiftMero a ha (b + a * h) := by
  rw [digammaScaleShiftMero, digammaScaleShiftMero, Differential.logDeriv,
    Differential.logDeriv, map_div₀, addTranslationMeroEquiv_deriv,
    addTranslationMeroEquiv_gammaScaleShiftMero_param a ha h b]

/-- The scale enters only through its value, not through the chosen nonvanishing witness. -/
theorem digammaScaleShiftMero_congr {a a' : ℂ} (ha : a ≠ 0) (ha' : a' ≠ 0) (h : a = a')
    (b : ℂ) : digammaScaleShiftMero a ha b = digammaScaleShiftMero a' ha' b := by
  subst h; rfl

theorem reciprocalGammaScaleShiftAnalytic_one (b : ℂ) :
    reciprocalGammaScaleShiftAnalytic 1 b = reciprocalGammaShiftAnalytic b := by
  apply Subtype.ext
  apply univGerm_ext
  intro z
  have hL : univGermEval z
      ((reciprocalGammaScaleShiftAnalytic 1 b : analyticSubring (Set.univ : Set ℂ)) :
        Filter.Germ (Filter.principal (Set.univ : Set ℂ)) ℂ)
      = reciprocalGammaEntire (1 * z + b) := rfl
  have hR : univGermEval z
      ((reciprocalGammaShiftAnalytic b : analyticSubring (Set.univ : Set ℂ)) :
        Filter.Germ (Filter.principal (Set.univ : Set ℂ)) ℂ)
      = reciprocalGammaEntire (z + b) := rfl
  rw [hL, hR, one_mul]

theorem gammaScaleShiftMero_one (b : ℂ) :
    gammaScaleShiftMero 1 one_ne_zero b = gammaShiftMero b := by
  rw [gammaScaleShiftMero_eq, reciprocalGammaScaleShiftAnalytic_one, gammaShiftMero]

theorem digammaScaleShiftMero_one (b : ℂ) :
    digammaScaleShiftMero 1 one_ne_zero b = digammaShiftMero b := by
  rw [digammaScaleShiftMero, gammaScaleShiftMero_one, digammaShiftMero]

/-! ## Differential algebraicity: the closure facts used below -/

theorem differentialAlgebraicOver_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → meroField (Set.univ : Set ℂ))
    (h : ∀ i ∈ s, DifferentialAlgebraicOver (RatFunc ℂ) (f i)) :
    DifferentialAlgebraicOver (RatFunc ℂ) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h0 : DifferentialAlgebraicOver (RatFunc ℂ)
          (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) 0) :=
        differentialAlgebraicOver_algebraMap 0
      simpa using h0
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      exact differentialAlgebraicOver_add (h a (Finset.mem_insert_self a t))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem differentialAlgebraicOver_neg_one_pow_mul {n : ℕ} {x : meroField (Set.univ : Set ℂ)}
    (hx : DifferentialAlgebraicOver (RatFunc ℂ) x) :
    DifferentialAlgebraicOver (RatFunc ℂ) ((-1 : meroField (Set.univ : Set ℂ)) ^ n * x) := by
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow, one_mul]; exact hx
  · rw [ho.neg_one_pow, neg_one_mul]; exact differentialAlgebraicOver_neg hx

theorem IsRationalMero.differentialAlgebraicOver {x : meroField (Set.univ : Set ℂ)}
    (hx : IsRationalMero x) : DifferentialAlgebraicOver (RatFunc ℂ) x := by
  obtain ⟨r, rfl⟩ := hx
  exact differentialAlgebraicOver_algebraMap r

/-! ## The digamma carrier of the ray product -/

/-- The translation step attached to the index `k`: the inverse of the `k`-th scale. -/
def rayStep (ω : ℂ) (k : ℕ) : ℂ := (ω ^ k)⁻¹

/-- The subset sum of the translation steps. -/
def raySubsetSum (ω : ℂ) (S : Finset ℕ) : ℂ := ∑ k ∈ S, rayStep ω k

/-- The digamma carrier `∑_{j<p} ψ(ω^j z + 1)` of the reciprocal-Gamma ray product. -/
def rayDigammaMero (p : ℕ) (ω : ℂ) (hω : ω ≠ 0) : meroField (Set.univ : Set ℂ) :=
  ∑ j ∈ Finset.range p, digammaScaleShiftMero (ω ^ j) (pow_ne_zero j hω) 1

/-- The logarithmic derivative of the ray product is minus its digamma carrier. -/
theorem logDeriv_gammaRayProductMero (p : ℕ) {ω : ℂ} (hω : ω ≠ 0) :
    Differential.logDeriv (gammaRayProductMero p ω hω) = -rayDigammaMero p ω hω := by
  classical
  rw [gammaRayProductMero, Differential.logDeriv_prod]
  · rw [rayDigammaMero, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hz : (gammaScaleShiftMero (ω ^ j) (pow_ne_zero j hω) 1)⁻¹
        = (gammaScaleShiftMero (ω ^ j) (pow_ne_zero j hω) 1) ^ (-1 : ℤ) := (zpow_neg_one _).symm
    rw [hz, differential_logDeriv_zpow _ (gammaScaleShiftMero_ne_zero _ _ _) (-1)]
    push_cast
    rw [neg_one_mul]
    rfl
  · intro j _
    exact inv_ne_zero (gammaScaleShiftMero_ne_zero _ _ _)

/-- Translating the digamma carrier moves each scale's parameter by that scale. -/
theorem addTranslationMeroEquiv_rayDigammaMero (p : ℕ) {ω : ℂ} (hω : ω ≠ 0) (h : ℂ) :
    addTranslationMeroEquiv h (rayDigammaMero p ω hω)
      = ∑ j ∈ Finset.range p,
          digammaScaleShiftMero (ω ^ j) (pow_ne_zero j hω) (1 + ω ^ j * h) := by
  rw [rayDigammaMero, map_sum]
  exact Finset.sum_congr rfl fun j _ =>
    addTranslationMeroEquiv_digammaScaleShiftMero_param _ _ h 1

/-! ## The omitted-factor difference operator -/

/-- The operator `∏_{k=1}^{p-1} (T_{ω^{-k}} − 1)` applied to the digamma carrier, expanded as an
alternating subset sum.  The index `k = 0` is deliberately omitted: no step of this family is
integral for the scale `ω^0 = 1`. -/
def rayDifference (p : ℕ) (ω : ℂ) (hω : ω ≠ 0) : meroField (Set.univ : Set ℂ) :=
  ∑ S ∈ (Finset.Ico 1 p).powerset,
    (-1 : meroField (Set.univ : Set ℂ)) ^ S.card
      * addTranslationMeroEquiv (raySubsetSum ω S) (rayDigammaMero p ω hω)

/-- The surviving common-scale component `∑_S (−1)^{|S|} ψ(z + 1 + σ_S)`. -/
def rayCommonPart (p : ℕ) (ω : ℂ) : meroField (Set.univ : Set ℂ) :=
  ∑ S ∈ (Finset.Ico 1 p).powerset,
    (-1 : meroField (Set.univ : Set ℂ)) ^ S.card * digammaShiftMero (1 + raySubsetSum ω S)

theorem rayDifference_eq_sum (p : ℕ) {ω : ℂ} (hω : ω ≠ 0) :
    rayDifference p ω hω
      = ∑ j ∈ Finset.range p, ∑ S ∈ (Finset.Ico 1 p).powerset,
          (-1 : meroField (Set.univ : Set ℂ)) ^ S.card
            * digammaScaleShiftMero (ω ^ j) (pow_ne_zero j hω)
                (1 + ω ^ j * raySubsetSum ω S) := by
  have hstep : ∀ S ∈ (Finset.Ico 1 p).powerset,
      (-1 : meroField (Set.univ : Set ℂ)) ^ S.card
          * addTranslationMeroEquiv (raySubsetSum ω S) (rayDigammaMero p ω hω)
        = ∑ j ∈ Finset.range p, (-1 : meroField (Set.univ : Set ℂ)) ^ S.card
            * digammaScaleShiftMero (ω ^ j) (pow_ne_zero j hω)
                (1 + ω ^ j * raySubsetSum ω S) := by
    intro S _
    rw [addTranslationMeroEquiv_rayDigammaMero, Finset.mul_sum]
  rw [rayDifference, Finset.sum_congr rfl hstep, Finset.sum_comm]

/-- **The rationalisation.**  All components of the difference operator except the common-scale
one are rational: for `j ≠ 0` the step `k = j` is integral for the scale `ω^j`. -/
theorem rayDifference_sub_rayCommonPart_isRational {p : ℕ} (hp : 0 < p) {ω : ℂ} (hω : ω ≠ 0) :
    IsRationalMero (rayDifference p ω hω - rayCommonPart p ω) := by
  classical
  have hins : Finset.range p = insert 0 (Finset.Ico 1 p) := by
    ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
  have h0 : (0 : ℕ) ∉ Finset.Ico 1 p := by simp
  rw [rayDifference_eq_sum p hω, hins, Finset.sum_insert h0]
  have hzero : ∑ S ∈ (Finset.Ico 1 p).powerset,
      (-1 : meroField (Set.univ : Set ℂ)) ^ S.card
        * digammaScaleShiftMero (ω ^ 0) (pow_ne_zero 0 hω) (1 + ω ^ 0 * raySubsetSum ω S)
      = rayCommonPart p ω := by
    rw [rayCommonPart]
    refine Finset.sum_congr rfl fun S _ => ?_
    congr 1
    rw [show (1 : ℂ) + ω ^ 0 * raySubsetSum ω S = 1 + raySubsetSum ω S by
      rw [pow_zero, one_mul]]
    rw [digammaScaleShiftMero_congr (pow_ne_zero 0 hω) one_ne_zero (pow_zero ω),
      digammaScaleShiftMero_one]
  rw [hzero, add_sub_cancel_left]
  refine IsRationalMero.sum _ _ fun j hj => ?_
  simp only [raySubsetSum]
  exact isRationalMero_alternating_digammaScaleShiftMero (ω ^ j) (pow_ne_zero j hω) 1
    (rayStep ω) (Finset.Ico 1 p) hj (mul_inv_cancel₀ (pow_ne_zero j hω))

theorem differentialAlgebraicOver_rayDifference (p : ℕ) {ω : ℂ} (hω : ω ≠ 0)
    (h : DifferentialAlgebraicOver (RatFunc ℂ) (rayDigammaMero p ω hω)) :
    DifferentialAlgebraicOver (RatFunc ℂ) (rayDifference p ω hω) := by
  rw [rayDifference]
  refine differentialAlgebraicOver_finset_sum _ _ fun S _ => ?_
  exact differentialAlgebraicOver_neg_one_pow_mul
    (differentialAlgebraicOver_addTranslationMeroEquiv _ h)

/-- If the digamma carrier is differentially algebraic, so is the common-scale combination. -/
theorem differentialAlgebraicOver_rayCommonPart {p : ℕ} (hp : 0 < p) {ω : ℂ} (hω : ω ≠ 0)
    (h : DifferentialAlgebraicOver (RatFunc ℂ) (rayDigammaMero p ω hω)) :
    DifferentialAlgebraicOver (RatFunc ℂ) (rayCommonPart p ω) := by
  have hd := differentialAlgebraicOver_rayDifference p hω h
  have hr := (rayDifference_sub_rayCommonPart_isRational hp hω).differentialAlgebraicOver
  have hsplit : rayCommonPart p ω
      = rayDifference p ω hω - (rayDifference p ω hω - rayCommonPart p ω) := by ring
  rw [hsplit]
  exact differentialAlgebraicOver_sub hd hr

/-! ## The orbit presentation -/

/-- The index equivalence from `Fin 2^{p-1}` onto the subsets of `{1,…,p−1}`. -/
def raySubsetEquiv (p : ℕ) :
    Fin ((Finset.Ico 1 p).powerset.card) ≃ {x // x ∈ (Finset.Ico 1 p).powerset} :=
  ((Finset.Ico 1 p).powerset.equivFin).symm

/-- The subset indexed by `c`. -/
def raySubsetOf (p : ℕ) (c : Fin ((Finset.Ico 1 p).powerset.card)) : Finset ℕ :=
  ((raySubsetEquiv p c : {x // x ∈ (Finset.Ico 1 p).powerset}) : Finset ℕ)

theorem raySubsetOf_subset (p : ℕ) (c : Fin ((Finset.Ico 1 p).powerset.card)) :
    raySubsetOf p c ⊆ Finset.Ico 1 p :=
  Finset.mem_powerset.mp (raySubsetEquiv p c).2

theorem raySubsetOf_injective (p : ℕ) : Function.Injective (raySubsetOf p) := by
  intro c c' h
  exact (raySubsetEquiv p).injective (Subtype.ext h)

/-- The orbit representatives `1 + σ_S`. -/
def rayOrbitBase (p : ℕ) (ω : ℂ) (c : Fin ((Finset.Ico 1 p).powerset.card)) : ℂ :=
  1 + raySubsetSum ω (raySubsetOf p c)

/-- The orbit charges `(−1)^{|S|}`. -/
def rayOrbitCharge (p : ℕ) (c : Fin ((Finset.Ico 1 p).powerset.card)) : ℂ :=
  (-1 : ℂ) ^ (raySubsetOf p c).card

theorem ratfuncToMero_C_neg_one_pow (n : ℕ) :
    ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty Set.infinite_univ
        (RatFunc.C ((-1 : ℂ) ^ n))
      = (-1 : meroField (Set.univ : Set ℂ)) ^ n := by
  rw [map_pow, map_neg, map_one, map_pow, map_neg, map_one]

/-- The common-scale combination is a finite separated-orbit digamma carrier. -/
theorem rayCommonPart_eq_gammaOrbitDigammaMero (p : ℕ) (ω : ℂ) :
    rayCommonPart p ω = gammaOrbitDigammaMero (rayOrbitBase p ω) (rayOrbitCharge p) := by
  classical
  rw [gammaOrbitDigammaMero]
  have hcomp := Equiv.sum_comp (raySubsetEquiv p)
    (fun x : {x // x ∈ (Finset.Ico 1 p).powerset} =>
      ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
          Set.infinite_univ (RatFunc.C ((-1 : ℂ) ^ ((x : Finset ℕ).card)))
        * digammaShiftMero (1 + raySubsetSum ω (x : Finset ℕ)))
  have hcoe := Finset.sum_coe_sort ((Finset.Ico 1 p).powerset)
    (fun S : Finset ℕ =>
      ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
          Set.infinite_univ (RatFunc.C ((-1 : ℂ) ^ S.card))
        * digammaShiftMero (1 + raySubsetSum ω S))
  rw [show (∑ c : Fin ((Finset.Ico 1 p).powerset.card),
        ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
            Set.infinite_univ (RatFunc.C (rayOrbitCharge p c))
          * digammaShiftMero (rayOrbitBase p ω c))
      = ∑ c : Fin ((Finset.Ico 1 p).powerset.card),
        ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
            Set.infinite_univ
            (RatFunc.C ((-1 : ℂ) ^ (((raySubsetEquiv p c : {x // x ∈ (Finset.Ico 1 p).powerset}) :
              Finset ℕ).card)))
          * digammaShiftMero
            (1 + raySubsetSum ω ((raySubsetEquiv p c : {x // x ∈ (Finset.Ico 1 p).powerset}) :
              Finset ℕ)) from rfl, hcomp, hcoe, rayCommonPart]
  exact Finset.sum_congr rfl fun S _ => by rw [ratfuncToMero_C_neg_one_pow]

/-! ## The imaginary-part functional and the shift-orbit separation -/

/-- For an odd exponent no scale on the ray is real. -/
theorem pow_im_ne_zero_of_odd {p : ℕ} (hodd : Odd p) {ω : ℂ} (hω : IsPrimitiveRoot ω p)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < p) : (ω ^ k).im ≠ 0 := by
  intro him
  have hnorm : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hω.pow_eq_one (by omega)
  have hnk : ‖ω ^ k‖ = 1 := by rw [norm_pow, hnorm, one_pow]
  have hreal : ω ^ k = (((ω ^ k).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hreal, Complex.norm_real] at hnk
  have hcases : (ω ^ k).re = 1 ∨ (ω ^ k).re = -1 :=
    (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hnk
  have hdvd : p ∣ k := by
    rcases hcases with h | h
    · rw [h] at hreal
      exact (hω.pow_eq_one_iff_dvd k).mp (by exact_mod_cast hreal)
    · have hm : ω ^ k = -1 := by rw [hreal, h]; norm_num
      have h2 : ω ^ (2 * k) = 1 := by rw [mul_comm, pow_mul, hm]; norm_num
      have hd2 := (hω.pow_eq_one_iff_dvd (2 * k)).mp h2
      have h2p : ¬ (2 ∣ p) := by
        intro hdd
        rcases hdd with ⟨m, rfl⟩
        rcases hodd with ⟨t, ht⟩
        omega
      have hcop : Nat.Coprime p 2 :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2p).symm
      exact hcop.dvd_of_dvd_mul_left hd2
  have := Nat.le_of_dvd (by omega) hdvd
  omega

/-- Every translation step of an odd ray has nonzero imaginary part. -/
theorem rayStep_im_ne_zero {p : ℕ} (hodd : Odd p) {ω : ℂ} (hω : IsPrimitiveRoot ω p)
    {k : ℕ} (hk : k ∈ Finset.Ico 1 p) : (rayStep ω k).im ≠ 0 := by
  obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
  have hne : ω ≠ 0 := hω.ne_zero (by omega)
  have hpow : (ω ^ k) ≠ 0 := pow_ne_zero _ hne
  rw [rayStep, Complex.inv_im]
  exact div_ne_zero (neg_ne_zero.mpr (pow_im_ne_zero_of_odd hodd hω hk1 hk2))
    (Complex.normSq_pos.mpr hpow).ne'

/-- The subset of indices whose translation step has positive imaginary part. -/
def rayMaxSubset (p : ℕ) (ω : ℂ) : Finset ℕ :=
  (Finset.Ico 1 p).filter (fun k => 0 < (rayStep ω k).im)

theorem rayMaxSubset_subset (p : ℕ) (ω : ℂ) : rayMaxSubset p ω ⊆ Finset.Ico 1 p :=
  Finset.filter_subset _ _

theorem raySubsetSum_im (ω : ℂ) (S : Finset ℕ) :
    (raySubsetSum ω S).im = ∑ k ∈ S, (rayStep ω k).im := by
  rw [raySubsetSum]
  simp [Complex.im_sum]

/-- **Strict maximality of the positive-part subset.**  For an odd exponent the imaginary part of
the subset sum of translation steps is strictly maximised by `rayMaxSubset`, and by it alone.  This
is the linear functional that separates the shift orbits: it kills `ℤ` and no step lies in its
kernel. -/
theorem raySubsetSum_im_lt {p : ℕ} (hodd : Odd p) {ω : ℂ} (hω : IsPrimitiveRoot ω p)
    {S : Finset ℕ} (hS : S ⊆ Finset.Ico 1 p) (hne : S ≠ rayMaxSubset p ω) :
    (raySubsetSum ω S).im < (raySubsetSum ω (rayMaxSubset p ω)).im := by
  classical
  set T := rayMaxSubset p ω with hT
  set f : ℕ → ℝ := fun k => (rayStep ω k).im with hf
  have hpos : ∀ k ∈ T, 0 < f k := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2
  have hnonpos : ∀ k ∈ S, k ∉ T → f k < 0 := by
    intro k hk hkT
    have hmem : k ∈ Finset.Ico 1 p := hS hk
    have hne0 : f k ≠ 0 := rayStep_im_ne_zero hodd hω hmem
    rcases lt_trichotomy (f k) 0 with h | h | h
    · exact h
    · exact absurd h hne0
    · exact absurd (Finset.mem_filter.mpr ⟨hmem, h⟩) hkT
  have hsplitT : ∑ k ∈ T \ S, f k + ∑ k ∈ T ∩ S, f k = ∑ k ∈ T, f k := by
    have h := Finset.sum_sdiff (s₁ := T ∩ S) (s₂ := T) Finset.inter_subset_left (f := f)
    rwa [Finset.sdiff_inter_self_left] at h
  have hsplitS : ∑ k ∈ S \ T, f k + ∑ k ∈ S ∩ T, f k = ∑ k ∈ S, f k := by
    have h := Finset.sum_sdiff (s₁ := S ∩ T) (s₂ := S) Finset.inter_subset_left (f := f)
    rwa [Finset.sdiff_inter_self_left] at h
  have hcomm : ∑ k ∈ S ∩ T, f k = ∑ k ∈ T ∩ S, f k := by rw [Finset.inter_comm]
  have hTSnn : 0 ≤ ∑ k ∈ T \ S, f k :=
    Finset.sum_nonneg fun k hk => le_of_lt (hpos k (Finset.mem_sdiff.mp hk).1)
  have hSTnp : ∑ k ∈ S \ T, f k ≤ 0 :=
    Finset.sum_nonpos fun k hk =>
      le_of_lt (hnonpos k (Finset.mem_sdiff.mp hk).1 (Finset.mem_sdiff.mp hk).2)
  have hstrict : ∑ k ∈ S \ T, f k < ∑ k ∈ T \ S, f k := by
    by_cases h1 : (T \ S).Nonempty
    · have : 0 < ∑ k ∈ T \ S, f k :=
        Finset.sum_pos (fun k hk => hpos k (Finset.mem_sdiff.mp hk).1) h1
      linarith
    · have hTS : T \ S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h1
      have h2 : (S \ T).Nonempty := by
        by_contra h2
        exact hne (Finset.Subset.antisymm
          (Finset.sdiff_eq_empty_iff_subset.mp (Finset.not_nonempty_iff_eq_empty.mp h2))
          (Finset.sdiff_eq_empty_iff_subset.mp hTS))
      have : ∑ k ∈ S \ T, f k < 0 :=
        Finset.sum_neg (fun k hk =>
          hnonpos k (Finset.mem_sdiff.mp hk).1 (Finset.mem_sdiff.mp hk).2) h2
      rw [hTS]
      simpa using this
  rw [raySubsetSum_im, raySubsetSum_im, ← hsplitS, ← hsplitT, hcomm]
  linarith

/-- The index of the positive-part subset. -/
def rayMaxIndex (p : ℕ) (ω : ℂ) : Fin ((Finset.Ico 1 p).powerset.card) :=
  (raySubsetEquiv p).symm ⟨rayMaxSubset p ω, Finset.mem_powerset.mpr (rayMaxSubset_subset p ω)⟩

theorem raySubsetOf_rayMaxIndex (p : ℕ) (ω : ℂ) :
    raySubsetOf p (rayMaxIndex p ω) = rayMaxSubset p ω := by
  rw [raySubsetOf, rayMaxIndex, Equiv.apply_symm_apply]

/-- **The orbits are separated.**  For an odd exponent the parameters `1 + σ_S` lie in `ℤ`-shift
orbits all distinct from the one carrying the positive-part subset. -/
theorem rayOrbitBase_separated {p : ℕ} (hodd : Odd p) {ω : ℂ} (hω : IsPrimitiveRoot ω p) :
    ∀ c, c ≠ rayMaxIndex p ω →
      ∀ n : ℤ, rayOrbitBase p ω c - rayOrbitBase p ω (rayMaxIndex p ω) ≠ (n : ℂ) := by
  intro c hc n heq
  have hS : raySubsetOf p c ⊆ Finset.Ico 1 p := raySubsetOf_subset p c
  have hne : raySubsetOf p c ≠ rayMaxSubset p ω := by
    rw [← raySubsetOf_rayMaxIndex p ω]
    exact fun h => hc (raySubsetOf_injective p h)
  have hlt := raySubsetSum_im_lt hodd hω hS hne
  rw [rayOrbitBase, rayOrbitBase, raySubsetOf_rayMaxIndex] at heq
  have him := congrArg Complex.im heq
  simp only [Complex.sub_im, Complex.add_im, Complex.one_im, Complex.intCast_im,
    zero_add] at him
  linarith

/-! ## Bank's theorem for an odd exponent -/

/-- **The digamma carrier of the ray product is hypertranscendental at an odd exponent.** -/
theorem hypertranscendentalOver_rayDigammaMero {p : ℕ} (hp : 1 < p) (hodd : Odd p) {ω : ℂ}
    (hω : IsPrimitiveRoot ω p) :
    HypertranscendentalOver (RatFunc ℂ) (rayDigammaMero p ω (hω.ne_zero (by omega))) := by
  intro hDA
  have hA := differentialAlgebraicOver_rayCommonPart (p := p) (by omega)
    (hω.ne_zero (by omega)) hDA
  rw [rayCommonPart_eq_gammaOrbitDigammaMero] at hA
  refine hypertranscendentalOver_gammaOrbitDigammaMero (rayOrbitBase p ω) (rayOrbitCharge p)
    (rayMaxIndex p ω) ?_ (rayOrbitBase_separated hodd hω) hA
  rw [rayOrbitCharge]
  exact pow_ne_zero _ (by norm_num)

/-- **The reciprocal-Gamma ray product is hypertranscendental at an odd exponent.** -/
theorem hypertranscendentalOver_gammaRayProductMero_odd {p : ℕ} (hp : 1 < p) (hodd : Odd p)
    {ω : ℂ} (hω : IsPrimitiveRoot ω p) :
    HypertranscendentalOver (RatFunc ℂ) (gammaRayProductMero p ω (hω.ne_zero (by omega))) := by
  have hne : ω ≠ 0 := hω.ne_zero (by omega)
  have hlog : HypertranscendentalOver (RatFunc ℂ)
      (Differential.logDeriv (gammaRayProductMero p ω hne)) := by
    rw [logDeriv_gammaRayProductMero]
    intro hDA
    exact hypertranscendentalOver_rayDigammaMero hp hodd hω
      (by simpa using differentialAlgebraicOver_neg hDA)
  exact (hypertranscendentalOver_deriv_div_self_iff _).mp hlog

/-- **The odd half of Bank's theorem.**  The canonical product with zeros `−n^p` is
hypertranscendental for every odd integer `p ≥ 3`. -/
theorem hypertranscendental_powerCanonicalProduct_odd {p : ℕ} (hp : 1 < p) (hodd : Odd p) :
    Hypertranscendental (powerCanonicalProduct (p : ℝ)) := by
  obtain ⟨ω, hω⟩ : ∃ ω : ℂ, IsPrimitiveRoot ω p :=
    ⟨_, Complex.isPrimitiveRoot_exp p (by omega)⟩
  rw [hypertranscendental_powerCanonicalProduct_odd_iff_mero hp hodd hω]
  exact hypertranscendentalOver_gammaRayProductMero_odd hp hodd hω

/-- **Bank's theorem.**  For a positive integer exponent, the canonical product with zeros `−n^p`
is differentially algebraic exactly when `p` is even. -/
theorem differentiallyAlgebraic_powerCanonicalProduct_natCast_iff {p : ℕ} (hp : 0 < p) :
    DifferentiallyAlgebraic (powerCanonicalProduct (p : ℝ)) ↔ Even p := by
  constructor
  · intro hDA
    by_contra hev
    rw [Nat.not_even_iff_odd] at hev
    rcases Nat.lt_or_ge p 2 with h1 | h2
    · have hp1 : p = 1 := by omega
      subst hp1
      exact hypertranscendental_powerCanonicalProduct_one (by simpa using hDA)
    · exact hypertranscendental_powerCanonicalProduct_odd (by omega) hev hDA
  · exact differentiallyAlgebraic_powerCanonicalProduct_of_even hp

/-- **Bank's theorem at a rational exponent with odd numerator.**  For every odd `p ≥ 3` and every
positive `q` the canonical product with zeros `−n^{p/q}` is hypertranscendental. -/
theorem hypertranscendental_powerCanonicalProduct_odd_ratio {p q : ℕ} (hp : 1 < p) (hodd : Odd p)
    (hq : 0 < q) :
    Hypertranscendental (powerCanonicalProduct ((p : ℝ) / (q : ℝ))) :=
  hypertranscendental_powerCanonicalProduct_ratio (by omega) hq
    (hypertranscendental_powerCanonicalProduct_odd hp hodd)

end

end HTGeometry
