import GaloisForLFunctions.ArithmeticPositiveDuality.HerglotzBochnerOnLattices
import GaloisForLFunctions.ArithmeticPositiveDuality.AffinePositivityIsInducedFromTheDilations
import GaloisForLFunctions.HTGeometry.InfiniteTorusFourierWeakConvergenceLaw

/-!
# Herglotz–Bochner on the positive rationals

The group `ℚ_{>0}` is free abelian on the primes, `u = Π_p p^{v_p(u)}`, of infinite rank. Its
dual group is the **prime torus** `𝕋^P = Π_p ℝ/ℤ`: the point `x` gives the character
`χ_x(u) = Π_p e^{2πi v_p(u) x_p}` (`ratChar`), the finite-support torus character of the
valuation vector `v(u)` (`valFinsupp`).

**Theorem** (`isPosDefOnGroup_posUnits_iff`). A function `f` on `ℚ_{>0}` is positive definite iff
`f(u) = ∫ χ_x(u) dμ(x)` for a finite positive measure `μ` on `𝕋^P`.

* (⇐) The Gram form is `∫ |Σ_b c_b χ_x(u_b)|² dμ`.
* (⇒) On the primes below `k`, `m ↦ f(Π_{p<k} p^{m_p})` is positive definite on `ℤ^{π(k)}`, so it
  is the coefficient sequence of a probability measure on `ℝ^{π(k)}`
  (`exists_probabilityMeasure_fourierCoeff_eq`). Its image on `𝕋^P` (coordinates `θ_p/2π` on the
  primes below `k`, `0` elsewhere) has the coefficients of `f` at every character supported below
  `k`. Each coefficient is eventually constant, so the Fourier–Lévy theorem of the prime torus
  (`existsUnique_probabilityMeasure_tendsto_of_infiniteTorusFourier_limit`) gives the limit law.

Every character of the prime torus is a valuation character (`valFinsupp_finsuppUnit`), so the
measure is unique (`probabilityMeasure_ext_of_infiniteTorusFourier_integral_eq`): the spectral
measure of a positive-definite function on `ℚ_{>0}` is well defined.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real BigOperators ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- The prime torus `Π_p ℝ/ℤ`, the dual group of `ℚ_{>0}`. -/
abbrev PrimeTorus := Nat.Primes → UnitAddCircle

/-! ### Valuation vectors -/

/-- The primes dividing the numerator or the denominator of `q`. -/
def primeSupp (q : ℚ) : Finset Nat.Primes :=
  (q.num.natAbs * q.den).primeFactors.preimage (fun p : Nat.Primes => (p : ℕ))
    Subtype.val_injective.injOn

theorem mem_primeSupp {q : ℚ} {p : Nat.Primes} :
    p ∈ primeSupp q ↔ (p : ℕ) ∈ (q.num.natAbs * q.den).primeFactors :=
  Finset.mem_preimage

theorem padicValRat_eq_zero_of_not_mem {q : ℚ} {p : Nat.Primes} (hp : p ∉ primeSupp q) :
    padicValRat p q = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hne : q.num.natAbs * q.den ≠ 0 :=
    mul_ne_zero (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq)) q.den_ne_zero
  have hnd : ¬ (p : ℕ) ∣ q.num.natAbs * q.den := fun h =>
    hp (mem_primeSupp.mpr (Nat.mem_primeFactors.mpr ⟨p.2, h, hne⟩))
  have h1 : ¬ (p : ℕ) ∣ q.num.natAbs := fun h => hnd (dvd_mul_of_dvd_left h _)
  have h2 : ¬ (p : ℕ) ∣ q.den := fun h => hnd (dvd_mul_of_dvd_right h _)
  rw [padicValRat_def, padicValInt, padicValNat.eq_zero_of_not_dvd h1,
    padicValNat.eq_zero_of_not_dvd h2]
  simp

/-- The valuation vector `(v_p(q))_p` of a rational. -/
def valFinsupp (q : ℚ) : Nat.Primes →₀ ℤ :=
  Finsupp.onFinset (primeSupp q) (fun p => padicValRat p q) fun p hp => by
    by_contra h
    exact hp (padicValRat_eq_zero_of_not_mem h)

@[simp]
theorem valFinsupp_apply (q : ℚ) (p : Nat.Primes) : valFinsupp q p = padicValRat p q := rfl

theorem valFinsupp_mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
    valFinsupp (q * r) = valFinsupp q + valFinsupp r := by
  ext p
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  simp [padicValRat.mul hq hr]

theorem valFinsupp_inv (q : ℚ) : valFinsupp q⁻¹ = -valFinsupp q := by
  ext p
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  simp

/-! ### Characters -/

/-- The character `χ_x(q) = Π_p e^{2πi v_p(q) x_p}` at a point `x` of the prime torus. -/
def ratChar (q : ℚ) (x : PrimeTorus) : ℂ := infiniteTorusFourier (valFinsupp q) x

theorem ratChar_mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) (x : PrimeTorus) :
    ratChar (q * r) x = ratChar q x * ratChar r x := by
  rw [ratChar, valFinsupp_mul hq hr, infiniteTorusFourier_add]; rfl

theorem ratChar_inv (q : ℚ) (x : PrimeTorus) : ratChar q⁻¹ x = conj (ratChar q x) := by
  rw [ratChar, valFinsupp_inv, infiniteTorusFourier_neg]; rfl

theorem continuous_ratChar (q : ℚ) : Continuous (ratChar q) :=
  (infiniteTorusFourier (valFinsupp q)).continuous

theorem ratChar_one (x : PrimeTorus) : ratChar 1 x = 1 := by
  have : valFinsupp 1 = 0 := by ext p; simp
  rw [ratChar, this, infiniteTorusFourier_zero]; rfl

theorem integrable_ratChar (μ : Measure PrimeTorus) [IsFiniteMeasure μ] (q : ℚ) :
    Integrable (ratChar q) μ :=
  (infiniteTorusFourier (valFinsupp q)).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The Gram form of `u ↦ ∫ χ_x(u) dμ` is `∫ |Σ_b c_b χ_x(u_b)|² dμ`. -/
theorem gram_integral_ratChar (μ : Measure PrimeTorus) [IsFiniteMeasure μ] {κ : Type*} [Fintype κ]
    (y : κ → posUnits) (c : κ → ℂ) :
    ∑ a, ∑ b, star (c a) * (∫ x, ratChar ((((y a)⁻¹ * y b : posUnits) : ℚˣ) : ℚ) x ∂μ) * c b =
      ((∫ x, Complex.normSq (∑ b, c b * ratChar ((y b : ℚˣ) : ℚ) x) ∂μ : ℝ) : ℂ) := by
  have hpt : ∀ x, ∑ a, ∑ b, star (c a) * ratChar (((y a)⁻¹ * y b : posUnits) : ℚˣ) x * c b =
      (Complex.normSq (∑ b, c b * ratChar ((y b : ℚˣ) : ℚ) x) : ℂ) := by
    intro x
    rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have ha : ((y a : ℚˣ) : ℚ) ≠ 0 := (y a : ℚˣ).ne_zero
    have hb : ((y b : ℚˣ) : ℚ) ≠ 0 := (y b : ℚˣ).ne_zero
    rw [show ((((y a)⁻¹ * y b : posUnits) : ℚˣ) : ℚ) = ((y a : ℚˣ) : ℚ)⁻¹ * ((y b : ℚˣ) : ℚ) by
      push_cast; rfl, ratChar_mul (inv_ne_zero ha) hb, ratChar_inv, map_mul]
    simp only [Complex.star_def]
    ring
  rw [← integral_complex_ofReal]
  simp_rw [← hpt]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    ((integrable_ratChar μ _).const_mul _).mul_const _]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => ((integrable_ratChar μ _).const_mul _).mul_const _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_mul_const, integral_const_mul]

/-- **Herglotz–Bochner on `ℚ_{>0}`, easy half.** -/
theorem isPosDefOnGroup_integral_ratChar (μ : Measure PrimeTorus) [IsFiniteMeasure μ] :
    IsPosDefOnGroup fun u : posUnits => ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂μ := fun _ y c =>
  ⟨_, integral_nonneg fun _ => Complex.normSq_nonneg _, gram_integral_ratChar μ y c⟩

/-! ### Finite-rank stages -/

/-- The primes below `k`. -/
def primeBox (k : ℕ) : Finset Nat.Primes :=
  (Finset.range k).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn

theorem mem_primeBox {k : ℕ} {p : Nat.Primes} : p ∈ primeBox k ↔ (p : ℕ) < k := by
  rw [primeBox, Finset.mem_preimage, Finset.mem_range]

theorem primeBox_mono {k k' : ℕ} (h : k ≤ k') : primeBox k ⊆ primeBox k' := fun p hp => by
  rw [mem_primeBox] at hp ⊢
  omega

theorem exists_support_subset_primeBox (n : Nat.Primes →₀ ℤ) : ∃ K, n.support ⊆ primeBox K :=
  ⟨n.support.sup (fun p => (p : ℕ)) + 1, fun p hp => by
    have := Finset.le_sup (f := fun p : Nat.Primes => (p : ℕ)) hp
    rw [mem_primeBox]
    omega⟩

/-- A prime as a positive rational unit. -/
def primeUnit (p : Nat.Primes) : posUnits :=
  ⟨Units.mk0 ((p : ℕ) : ℚ) (by exact_mod_cast p.2.ne_zero), by
    show (0 : ℚ) < ((p : ℕ) : ℚ); exact_mod_cast p.2.pos⟩

/-- The rational `Π_{p < k} p^{m_p}`. -/
def latticeHom (k : ℕ) (m : primeBox k → ℤ) : posUnits := ∏ p : primeBox k, primeUnit p ^ m p

theorem latticeHom_add (k : ℕ) (m m' : primeBox k → ℤ) :
    latticeHom k (m + m') = latticeHom k m * latticeHom k m' := by
  simp only [latticeHom, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem latticeHom_zero (k : ℕ) : latticeHom k 0 = 1 := by
  simp [latticeHom]

theorem latticeHom_sub (k : ℕ) (m m' : primeBox k → ℤ) :
    latticeHom k (m' - m) = (latticeHom k m)⁻¹ * latticeHom k m' := by
  have h := latticeHom_add k (m' - m) m
  rw [sub_add_cancel] at h
  rw [h, mul_comm (latticeHom k (m' - m)), inv_mul_cancel_left]

/-- Restricted to the primes below `k`, a positive-definite function on `ℚ_{>0}` is positive
definite on `ℤ^{π(k)}`. -/
theorem IsPosDefOnGroup.comp_latticeHom {f : posUnits → ℂ} (hf : IsPosDefOnGroup f) (k : ℕ) :
    IsPosDefOnLattice fun m : primeBox k → ℤ => f (latticeHom k m) := by
  intro N x c
  obtain ⟨r, hr, h⟩ := hf N (fun a => latticeHom k (x a)) c
  exact ⟨r, hr, by rw [← h]; simp_rw [latticeHom_sub]⟩

/-- A positive-definite function on `ℚ_{>0}` is bounded by its value at `1`. -/
theorem IsPosDefOnGroup.norm_le_posUnits {f : posUnits → ℂ} (hf : IsPosDefOnGroup f)
    (g : posUnits) : ‖f g‖ ≤ (f 1).re := by
  have hL : IsPosDefOnLattice (ι := Fin 1) fun m => f (g ^ (m 0)) := by
    intro N x c
    obtain ⟨r, hr, h⟩ := hf N (fun a => g ^ (x a 0)) c
    refine ⟨r, hr, ?_⟩
    rw [← h]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Pi.sub_apply, zpow_sub, mul_comm (g ^ x b 0)]
  simpa using hL.norm_le (fun _ => 1)

/-- The rational `Π_p p^{n_p}` of a finitely supported exponent vector. -/
def finsuppUnit (n : Nat.Primes →₀ ℤ) : posUnits := n.prod fun p k => primeUnit p ^ k

theorem finsuppUnit_eq_latticeHom {n : Nat.Primes →₀ ℤ} {k : ℕ} (h : n.support ⊆ primeBox k) :
    finsuppUnit n = latticeHom k fun p => n p := by
  rw [finsuppUnit, Finsupp.prod_of_support_subset n h (fun p k => primeUnit p ^ k)
    (fun _ _ => zpow_zero _), latticeHom, ← Finset.prod_coe_sort]

theorem val_finsuppUnit (n : Nat.Primes →₀ ℤ) :
    (((finsuppUnit n : posUnits) : ℚˣ) : ℚ) = ∏ p ∈ n.support, ((p : ℕ) : ℚ) ^ n p := by
  simp [finsuppUnit, Finsupp.prod, primeUnit]

/-- For natural `a ≠ 0` whose primes lie in `T`, `Π_{p ∈ T} p^{v_p(a)} = a`. -/
theorem prod_pow_padicValNat {a : ℕ} (ha : a ≠ 0) {T : Finset Nat.Primes}
    (hT : ∀ p : Nat.Primes, (p : ℕ) ∣ a → p ∈ T) :
    ∏ p ∈ T, (((p : ℕ) : ℚ) ^ padicValNat p a) = a := by
  have hfac : (∏ p ∈ a.primeFactors, p ^ a.factorization p) = a := by
    have := Nat.prod_factorization_pow_eq_self ha
    rwa [Finsupp.prod, Nat.support_factorization] at this
  set e : Nat.Primes ↪ ℕ := ⟨fun p => (p : ℕ), Subtype.val_injective⟩ with he
  have hsub : a.primeFactors ⊆ T.map e := fun p hp => by
    rw [Nat.mem_primeFactors] at hp
    exact Finset.mem_map.mpr ⟨⟨p, hp.1⟩, hT ⟨p, hp.1⟩ hp.2.1, rfl⟩
  have e1 : ∏ p ∈ T, (((p : ℕ) : ℚ) ^ padicValNat p a) =
      ∏ p ∈ T.map e, ((p : ℚ) ^ padicValNat p a) := by
    rw [Finset.prod_map]; rfl
  rw [e1, ← Finset.prod_subset hsub]
  · have : ∀ p ∈ a.primeFactors, ((p : ℚ) ^ padicValNat p a) = ((p ^ a.factorization p : ℕ) : ℚ) :=
      fun p hp => by
        rw [Nat.factorization_def a (Nat.prime_of_mem_primeFactors hp)]; push_cast; rfl
    rw [Finset.prod_congr rfl this, ← Nat.cast_prod, hfac]
  · intro p hpT hpa
    obtain ⟨p', -, rfl⟩ := Finset.mem_map.mp hpT
    have hnd : ¬ (p' : ℕ) ∣ a := fun h => hpa (Nat.mem_primeFactors.mpr ⟨p'.2, h, ha⟩)
    show ((p' : ℕ) : ℚ) ^ padicValNat (p' : ℕ) a = 1
    rw [padicValNat.eq_zero_of_not_dvd hnd, pow_zero]

/-- **Unique factorization over `ℚ_{>0}`**: `Π_{p ∈ T} p^{v_p(q)} = q` for `T` containing the
primes of `q`. -/
theorem prod_zpow_padicValRat {q : ℚ} (hq0 : 0 < q) {T : Finset Nat.Primes}
    (hT : primeSupp q ⊆ T) : ∏ p ∈ T, ((p : ℕ) : ℚ) ^ padicValRat p q = q := by
  have hnum : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq0.le)
  have ha : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq0.ne')
  have hmem : ∀ p : Nat.Primes, (p : ℕ) ∣ q.num.natAbs * q.den → p ∈ T := fun p h =>
    hT (mem_primeSupp.mpr (Nat.mem_primeFactors.mpr ⟨p.2, h, mul_ne_zero ha q.den_ne_zero⟩))
  have hA := prod_pow_padicValNat ha fun p h => hmem p (dvd_mul_of_dvd_left h _)
  have hB := prod_pow_padicValNat q.den_ne_zero fun p h => hmem p (dvd_mul_of_dvd_right h _)
  have hpow : ∀ p ∈ T, ((p : ℕ) : ℚ) ^ padicValRat p q =
      ((p : ℕ) : ℚ) ^ padicValNat p q.num.natAbs / ((p : ℕ) : ℚ) ^ padicValNat p q.den := by
    intro p _
    have hp0 : ((p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    rw [padicValRat_def, padicValInt, zpow_sub₀ hp0, zpow_natCast, zpow_natCast]
  rw [Finset.prod_congr rfl hpow, Finset.prod_div_distrib, hA, hB]
  have hnQ : ((q.num.natAbs : ℕ) : ℚ) = (q.num : ℚ) := by
    rw [Nat.cast_natAbs, abs_of_nonneg (by exact_mod_cast Rat.num_nonneg.mpr hq0.le)]
  rw [hnQ]
  exact Rat.num_div_den q

/-- `u = Π_p p^{v_p(u)}`. -/
theorem finsuppUnit_valFinsupp (u : posUnits) : finsuppUnit (valFinsupp ((u : ℚˣ) : ℚ)) = u := by
  refine Subtype.ext (Units.ext ?_)
  rw [val_finsuppUnit]
  have hsub : (valFinsupp ((u : ℚˣ) : ℚ)).support ⊆ primeSupp ((u : ℚˣ) : ℚ) := fun p hp => by
    by_contra h
    exact Finsupp.mem_support_iff.mp hp (padicValRat_eq_zero_of_not_mem h)
  have := prod_zpow_padicValRat u.2 (subset_refl (primeSupp ((u : ℚˣ) : ℚ)))
  rw [← Finset.prod_subset hsub fun p _ hp => by
    rw [← valFinsupp_apply, Finsupp.notMem_support_iff.mp hp, zpow_zero]] at this
  exact this

/-- `v_p(Π_q q^{n_q}) = n_p`: every torus character is a valuation character. -/
theorem valFinsupp_finsuppUnit (n : Nat.Primes →₀ ℤ) :
    valFinsupp (((finsuppUnit n : posUnits) : ℚˣ) : ℚ) = n := by
  ext p
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  rw [valFinsupp_apply, val_finsuppUnit]
  have hval : ∀ s : Finset Nat.Primes, padicValRat p (∏ q ∈ s, ((q : ℕ) : ℚ) ^ n q) =
      ∑ q ∈ s, n q * (if q = p then 1 else 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert q s hq ih =>
      have hq0 : ((q : ℕ) : ℚ) ^ n q ≠ 0 := zpow_ne_zero _ (by exact_mod_cast q.2.ne_zero)
      have hs0 : ∏ q ∈ s, ((q : ℕ) : ℚ) ^ n q ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun r _ => zpow_ne_zero _ (by exact_mod_cast r.2.ne_zero)
      rw [Finset.prod_insert hq, padicValRat.mul hq0 hs0, Finset.sum_insert hq, ih,
        padicValRat.zpow, padicValRat.of_nat]
      congr 1
      by_cases hqp : q = p
      · subst hqp; simp [padicValNat_self]
      · haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
        have hne : (p : ℕ) ≠ (q : ℕ) := fun h => hqp (Subtype.ext h).symm
        simp [hqp, padicValNat_primes hne]
  rw [hval]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  split_ifs with hp
  · ring
  · rw [Finsupp.notMem_support_iff.mp hp]

/-- The finite stage on the prime torus: coordinates `θ_p/2π` on the primes below `k`, all others
`0`. -/
def boxLift (k : ℕ) (θ : primeBox k → ℝ) : PrimeTorus := fun p =>
  if h : p ∈ primeBox k then ((θ ⟨p, h⟩ / (2 * π) : ℝ) : UnitAddCircle) else 0

theorem measurable_boxLift (k : ℕ) : Measurable (boxLift k) := by
  refine measurable_pi_lambda _ fun p => ?_
  by_cases h : p ∈ primeBox k
  · simp only [boxLift, dif_pos h]
    exact AddCircle.measurable_mk'.comp ((measurable_pi_apply _).div_const _)
  · simp only [boxLift, dif_neg h]
    exact measurable_const

/-- On the finite stage a torus character is the lattice character of its exponent vector. -/
theorem infiniteTorusFourier_boxLift {n : Nat.Primes →₀ ℤ} {k : ℕ} (h : n.support ⊆ primeBox k)
    (θ : primeBox k → ℝ) :
    infiniteTorusFourier n (boxLift k θ) = latticeChar (fun p : primeBox k => n p) θ := by
  simp only [infiniteTorusFourier, ContinuousMap.coe_mk]
  rw [Finsupp.prod_of_support_subset n h _ fun _ _ => fourier_zero, ← Finset.prod_coe_sort,
    latticeChar_eq_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [boxLift, dif_pos p.2, fourier_coe_apply]
  congr 1
  push_cast
  field_simp

/-! ### The hard half -/

/-- **Herglotz–Bochner on `ℚ_{>0}`, normalized.** A positive-definite `f` on `ℚ_{>0}` with
`f(1) = 1` is `u ↦ ∫ χ_x(u) dμ(x)` for a probability measure `μ` on the prime torus. -/
theorem exists_probabilityMeasure_ratChar {f : posUnits → ℂ} (hf : IsPosDefOnGroup f)
    (hf1 : f 1 = 1) :
    ∃ μ : ProbabilityMeasure PrimeTorus,
      ∀ u : posUnits, ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂(μ : Measure PrimeTorus) = f u := by
  have hstage : ∀ k : ℕ, ∃ ν : ProbabilityMeasure (primeBox k → ℝ),
      ∀ m, fourierCoeff (ν : Measure (primeBox k → ℝ)) m = f (latticeHom k m) := fun k =>
    exists_probabilityMeasure_fourierCoeff_eq (hf.comp_latticeHom k)
      (by simp only [latticeHom_zero, hf1])
  choose ν hν using hstage
  set seq : ℕ → ProbabilityMeasure PrimeTorus := fun k =>
    (ν k).map (measurable_boxLift k).aemeasurable with hseq_def
  have hlim : ∀ n : Nat.Primes →₀ ℤ, Tendsto
      (fun k => ∫ x, infiniteTorusFourier n x ∂(seq k : Measure PrimeTorus)) atTop
        (𝓝 (f (finsuppUnit n))) := by
    intro n
    obtain ⟨K, hK⟩ := exists_support_subset_primeBox n
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop K] with k hk
    have hsub := hK.trans (primeBox_mono hk)
    rw [show ((seq k : ProbabilityMeasure PrimeTorus) : Measure PrimeTorus) =
      (ν k : Measure (primeBox k → ℝ)).map (boxLift k) from ProbabilityMeasure.toMeasure_map _ _,
      integral_map (measurable_boxLift k).aemeasurable
        (infiniteTorusFourier n).continuous.aestronglyMeasurable]
    simp_rw [infiniteTorusFourier_boxLift hsub]
    rw [show (∫ θ, latticeChar (fun p : primeBox k => n p) θ ∂(ν k : Measure (primeBox k → ℝ))) =
      fourierCoeff (ν k : Measure (primeBox k → ℝ)) (fun p => n p) from rfl, hν k,
      finsuppUnit_eq_latticeHom hsub]
  obtain ⟨μ, ⟨-, hμ⟩, -⟩ :=
    existsUnique_probabilityMeasure_tendsto_of_infiniteTorusFourier_limit seq _ hlim
  refine ⟨μ, fun u => ?_⟩
  rw [show (fun x => ratChar ((u : ℚˣ) : ℚ) x) = infiniteTorusFourier (valFinsupp ((u : ℚˣ) : ℚ))
    from rfl, hμ, finsuppUnit_valFinsupp]

/-- **Herglotz–Bochner on `ℚ_{>0}`.** A positive-definite function on `ℚ_{>0}` is
`u ↦ ∫ χ_x(u) dμ(x)` for a finite positive measure on the prime torus. -/
theorem exists_measure_ratChar {f : posUnits → ℂ} (hf : IsPosDefOnGroup f) :
    ∃ μ : Measure PrimeTorus, IsFiniteMeasure μ ∧
      ∀ u : posUnits, f u = ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂μ := by
  obtain ⟨p, hp0, h1⟩ : ∃ p : ℝ, 0 ≤ p ∧ f 1 = p := by
    obtain ⟨r, hr, h⟩ := hf 1 ![1] ![1]
    exact ⟨r, hr, by simpa using h⟩
  rcases hp0.lt_or_eq with hpos | hzero
  · have hg : IsPosDefOnGroup fun u => ((1 / p : ℝ) : ℂ) * f u := by
      intro N x c
      obtain ⟨r, hr, h⟩ := hf N x c
      refine ⟨(1 / p) * r, mul_nonneg (by positivity) hr, ?_⟩
      push_cast
      rw [← h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hg1 : ((1 / p : ℝ) : ℂ) * f 1 = 1 := by
      rw [h1]; push_cast; field_simp
    obtain ⟨μ₀, hμ₀⟩ := exists_probabilityMeasure_ratChar hg hg1
    refine ⟨ENNReal.ofReal p • (μ₀ : Measure PrimeTorus), ⟨?_⟩, fun u => ?_⟩
    · rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
    rw [integral_smul_measure, hμ₀ u, ENNReal.toReal_ofReal hpos.le, Complex.real_smul]
    push_cast
    field_simp
  · refine ⟨0, inferInstance, fun u => ?_⟩
    have := hf.norm_le_posUnits u
    rw [h1, ← hzero, Complex.ofReal_re] at this
    rw [norm_le_zero_iff.mp this, integral_zero_measure]

/-- **Herglotz–Bochner on `ℚ_{>0}`, both directions.** -/
theorem isPosDefOnGroup_posUnits_iff (f : posUnits → ℂ) :
    IsPosDefOnGroup f ↔ ∃ μ : Measure PrimeTorus, IsFiniteMeasure μ ∧
      ∀ u : posUnits, f u = ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂μ := by
  constructor
  · exact exists_measure_ratChar
  · rintro ⟨μ, hμ, hf⟩
    rw [show f = fun u : posUnits => ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂μ from funext hf]
    exact isPosDefOnGroup_integral_ratChar μ

/-- **Uniqueness.** A probability measure on the prime torus is determined by its values on the
valuation characters. -/
theorem probabilityMeasure_ext_of_ratChar {μ ν : ProbabilityMeasure PrimeTorus}
    (h : ∀ u : posUnits, ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂(μ : Measure PrimeTorus) =
      ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂(ν : Measure PrimeTorus)) : μ = ν := by
  refine probabilityMeasure_ext_of_infiniteTorusFourier_integral_eq μ ν fun n => ?_
  have key : ∀ x, ratChar (((finsuppUnit n : posUnits) : ℚˣ) : ℚ) x = infiniteTorusFourier n x :=
    fun x => by rw [ratChar, valFinsupp_finsuppUnit]
  have := h (finsuppUnit n)
  simp_rw [key] at this
  exact this

/-- **Uniqueness for finite measures.** A finite measure on the prime torus is determined by its
values on the valuation characters. -/
theorem finiteMeasure_ext_of_ratChar {μ ν : Measure PrimeTorus} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ u : posUnits, ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂μ = ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂ν) :
    μ = ν := by
  have hmass : μ univ = ν univ := by
    have h1 := h 1
    simp only [OneMemClass.coe_one, Units.val_one, ratChar_one, integral_const,
      Complex.real_smul, mul_one] at h1
    have : μ.real univ = ν.real univ := by exact_mod_cast h1
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp this
  by_cases h0 : μ univ = 0
  · have hμ0 : μ = 0 := Measure.measure_univ_eq_zero.mp h0
    have hν0 : ν = 0 := Measure.measure_univ_eq_zero.mp (by rw [← hmass]; exact h0)
    rw [hμ0, hν0]
  · have hc : μ univ ≠ ⊤ := measure_ne_top _ _
    have hP : IsProbabilityMeasure ((μ univ)⁻¹ • μ) :=
      ⟨by rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 hc]⟩
    have hQ : IsProbabilityMeasure ((μ univ)⁻¹ • ν) :=
      ⟨by rw [Measure.smul_apply, smul_eq_mul, ← hmass, ENNReal.inv_mul_cancel h0 hc]⟩
    have heq := probabilityMeasure_ext_of_ratChar (μ := ⟨_, hP⟩) (ν := ⟨_, hQ⟩) fun u => by
      simp only [ProbabilityMeasure.coe_mk, integral_smul_measure, h u]
    have := congrArg (fun ρ : ProbabilityMeasure PrimeTorus => (μ univ) • (ρ : Measure PrimeTorus))
      heq
    simpa [smul_smul, ENNReal.mul_inv_cancel h0 hc] using this

end GaloisForLFunctions.ArithmeticPositiveDuality
