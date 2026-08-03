import GaloisForLFunctions.HTGeometry.MeromorphicGammaComplexScale
import GaloisForLFunctions.HTGeometry.CyclotomicSubsetSumOrbit
import GaloisForLFunctions.HTGeometry.TranslationStableDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.SourceLogarithmicBoundary

/-!
# The reciprocal-Gamma ray product at an odd prime is hypertranscendental

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

For `p` prime the arithmetic of `ℤ[ζ_p]` says `σ_S − σ_{S'} ∈ ℤ` only when `S = S'` or
`{S,S'} = {∅, {1,…,p−1}}`; hence the shift orbits of the parameters `1 + σ_S` are separated once a
subset other than `∅` and `{1,…,p−1}` is singled out, and every charge `(−1)^{|S|}` is nonzero.  The
separated-orbit Gamma law then makes `A` hypertranscendental, contradicting its differential
algebraicity.  So `Φ`, hence the ray product, hence the canonical product `W_p` with zeros `−n^p`,
is hypertranscendental for every odd prime `p`.
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

/-! ## The reversal involution and the shift-orbit separation -/

/-- The reversal `k ↦ p − k`, an involution of `{1,…,p−1}`. -/
def rayReverse (p : ℕ) (S : Finset ℕ) : Finset ℕ := S.image (fun k => p - k)

theorem rayReverse_subset {p : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ico 1 p) :
    rayReverse p S ⊆ Finset.Ico 1 p := by
  intro x hx
  rw [rayReverse, Finset.mem_image] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  have := Finset.mem_Ico.mp (hS hk)
  exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩

theorem rayReverse_rayReverse {p : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ico 1 p) :
    rayReverse p (rayReverse p S) = S := by
  ext x
  simp only [rayReverse, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨k, hk, rfl⟩, rfl⟩
    have := Finset.mem_Ico.mp (hS hk)
    rwa [show p - (p - k) = k by omega]
  · intro hx
    have := Finset.mem_Ico.mp (hS hx)
    exact ⟨p - x, ⟨x, hx, rfl⟩, by omega⟩

theorem rayReverse_empty (p : ℕ) : rayReverse p (∅ : Finset ℕ) = ∅ := by
  simp [rayReverse]

theorem rayReverse_eq_empty_iff {p : ℕ} {S : Finset ℕ} : rayReverse p S = ∅ ↔ S = ∅ := by
  rw [rayReverse]
  exact Finset.image_eq_empty

theorem rayReverse_Ico (p : ℕ) : rayReverse p (Finset.Ico 1 p) = Finset.Ico 1 p := by
  ext x
  simp only [rayReverse, Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
    exact ⟨by omega, by omega⟩
  · rintro ⟨hx1, hx2⟩
    exact ⟨p - x, ⟨by omega, by omega⟩, by omega⟩

/-- The subset sum of the steps is a subset sum of powers of `ω` over the reversed index set. -/
theorem raySubsetSum_eq_sum_pow {p : ℕ} {ω : ℂ} (hω : IsPrimitiveRoot ω p) (hp : 0 < p)
    {S : Finset ℕ} (hS : S ⊆ Finset.Ico 1 p) :
    raySubsetSum ω S = ∑ m ∈ rayReverse p S, ω ^ m := by
  have hne : ω ≠ 0 := hω.ne_zero (by omega)
  have hinj : Set.InjOn (fun k => p - k) (S : Set ℕ) := by
    intro a ha b hb hab
    have h1 := Finset.mem_Ico.mp (hS ha)
    have h2 := Finset.mem_Ico.mp (hS hb)
    simp only at hab
    omega
  rw [rayReverse, Finset.sum_image hinj, raySubsetSum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_Ico.mp (hS hk)
  rw [rayStep]
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [← pow_add, show p - k + k = p by omega, hω.pow_eq_one]

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

/-! ## The separation, and hypertranscendence -/

/-- A distinguished index: the singleton `{1}`, which is neither empty nor the whole family. -/
def raySingletonIndex {p : ℕ} (hp : 3 ≤ p) : Fin ((Finset.Ico 1 p).powerset.card) :=
  (raySubsetEquiv p).symm ⟨{1}, Finset.mem_powerset.mpr (by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_Ico.mpr ⟨le_refl 1, by omega⟩)⟩

theorem raySubsetOf_raySingletonIndex {p : ℕ} (hp : 3 ≤ p) :
    raySubsetOf p (raySingletonIndex hp) = {1} := by
  rw [raySubsetOf, raySingletonIndex, Equiv.apply_symm_apply]

/-- **The orbits are separated.**  For `p` prime the parameters `1 + σ_S` lie in pairwise distinct
`ℤ`-shift orbits once the singleton `{1}` is taken as the reference. -/
theorem rayOrbitBase_separated {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) {ω : ℂ}
    (hω : IsPrimitiveRoot ω p) :
    ∀ c, c ≠ raySingletonIndex hp →
      ∀ n : ℤ, rayOrbitBase p ω c - rayOrbitBase p ω (raySingletonIndex hp) ≠ (n : ℂ) := by
  intro c hc n heq
  set c0 := raySingletonIndex hp with hc0def
  have hS : raySubsetOf p c ⊆ Finset.Ico 1 p := raySubsetOf_subset p c
  have hS0 : raySubsetOf p c0 ⊆ Finset.Ico 1 p := raySubsetOf_subset p c0
  have hsum : (∑ m ∈ rayReverse p (raySubsetOf p c), ω ^ m)
      - (∑ m ∈ rayReverse p (raySubsetOf p c0), ω ^ m) = (n : ℂ) := by
    rw [← raySubsetSum_eq_sum_pow hω (by omega) hS, ← raySubsetSum_eq_sum_pow hω (by omega) hS0]
    rw [rayOrbitBase, rayOrbitBase] at heq
    linear_combination heq
  have hsing : raySubsetOf p c0 = {1} := raySubsetOf_raySingletonIndex hp
  rcases subsetSum_sub_eq_intCast_cases hω (rayReverse_subset hS) (rayReverse_subset hS0) hsum with
    heqS | ⟨hemp, hfull⟩ | ⟨hfull, hemp⟩
  · exact hc (raySubsetOf_injective p (by
      rw [← rayReverse_rayReverse hS, ← rayReverse_rayReverse hS0, heqS]))
  · -- the reference subset would have to be the whole family
    have : raySubsetOf p c0 = Finset.Ico 1 p := by
      rw [← rayReverse_rayReverse hS0, hfull, rayReverse_Ico]
    rw [hsing] at this
    have h2 : (2 : ℕ) ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    rw [← this, Finset.mem_singleton] at h2
    omega
  · -- the reference subset would have to be empty
    have : raySubsetOf p c0 = ∅ := rayReverse_eq_empty_iff.mp hemp
    rw [hsing] at this
    exact absurd this (by simp)

/-- **The digamma carrier of the ray product is hypertranscendental at an odd prime.** -/
theorem hypertranscendentalOver_rayDigammaMero {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) {ω : ℂ}
    (hω : IsPrimitiveRoot ω p) :
    HypertranscendentalOver (RatFunc ℂ) (rayDigammaMero p ω (hω.ne_zero (by omega))) := by
  intro hDA
  have hA := differentialAlgebraicOver_rayCommonPart (p := p) (by omega)
    (hω.ne_zero (by omega)) hDA
  rw [rayCommonPart_eq_gammaOrbitDigammaMero] at hA
  refine hypertranscendentalOver_gammaOrbitDigammaMero (rayOrbitBase p ω) (rayOrbitCharge p)
    (raySingletonIndex hp) ?_ (rayOrbitBase_separated hp hω) hA
  rw [rayOrbitCharge]
  exact pow_ne_zero _ (by norm_num)

/-- **The reciprocal-Gamma ray product is hypertranscendental at an odd prime.** -/
theorem hypertranscendentalOver_gammaRayProductMero_prime {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    {ω : ℂ} (hω : IsPrimitiveRoot ω p) :
    HypertranscendentalOver (RatFunc ℂ) (gammaRayProductMero p ω (hω.ne_zero (by omega))) := by
  have hne : ω ≠ 0 := hω.ne_zero (by omega)
  have hlog : HypertranscendentalOver (RatFunc ℂ)
      (Differential.logDeriv (gammaRayProductMero p ω hne)) := by
    rw [logDeriv_gammaRayProductMero]
    intro hDA
    exact hypertranscendentalOver_rayDigammaMero hp hω
      (by simpa using differentialAlgebraicOver_neg hDA)
  exact (hypertranscendentalOver_deriv_div_self_iff _).mp hlog

/-- **Bank's theorem at an odd prime exponent.**  The canonical product with zeros `−n^p` is
hypertranscendental for every prime `p ≥ 3`. -/
theorem hypertranscendental_powerCanonicalProduct_prime {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) :
    Hypertranscendental (powerCanonicalProduct (p : ℝ)) := by
  obtain ⟨ω, hω⟩ : ∃ ω : ℂ, IsPrimitiveRoot ω p :=
    ⟨_, Complex.isPrimitiveRoot_exp p (by omega)⟩
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rw [hypertranscendental_powerCanonicalProduct_odd_iff_mero (by omega) hodd hω]
  exact hypertranscendentalOver_gammaRayProductMero_prime hp hω

/-- **Bank's theorem at an odd-prime numerator.**  For every prime `p ≥ 3` and every positive `q`
the canonical product with zeros `−n^{p/q}` is hypertranscendental. -/
theorem hypertranscendental_powerCanonicalProduct_prime_ratio {p q : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (hq : 0 < q) :
    Hypertranscendental (powerCanonicalProduct ((p : ℝ) / (q : ℝ))) :=
  hypertranscendental_powerCanonicalProduct_ratio (by omega) hq
    (hypertranscendental_powerCanonicalProduct_prime hp)

end

end HTGeometry
