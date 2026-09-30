import GaloisForLFunctions.RHTower.ZetaNotchPairingInequality

/-!
# The Bohr lift of the `|ζ|²` diagonal over a finite set of primes

Fix a finite set `P` of primes and write twists of the multiplicative group `⟨P⟩ ⊂ ℚ_{>0}` as
exponent vectors `a : P → ℤ`, with frequency `λ(a) = Σ_p a_p log p`. The reduced numerator and
denominator `h(a) = Π p^{a_p⁺}`, `k(a) = Π p^{a_p⁻}` are coprime (`coprime_vecNum_vecDen`),
`λ(a) = log h(a) − log k(a)` (`vecFreq_eq`), and `(h(a)k(a))^{−1/2} = Π_p s_p^{|a_p|}` with
`s_p = p^{−1/2}` (`inv_sqrt_vecNum_mul_vecDen`).

The Euler factor `|1 − s e^{iθ}|² = (1 + s²) − s e^{iθ} − s e^{−iθ}` annihilates the Poisson
sequence `s^{|m|}` off the origin (`sum_bohrCoeff_mul_pow`):

`(1 + s²) s^{|m|} − s (s^{|m−1|} + s^{|m+1|}) = (1 − s²) [m = 0]`.

Over `P` this gives (`sum_bohrVec_mul_prod_pow`)

`Σ_{c ∈ {−1,0,1}^P} Π_p e_{c_p}(s_p) · Π_p s_p^{|a_p − c_p|} = Π_p (1 − s_p²) · [a = 0]`,

the cancellation of the Bohr lift of the `|ζ|²` diagonal by the Euler factors at `P`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.ZetaNotch

open RHTower.SmoothNumbers

/-! ## Exponent vectors -/

/-- `s_p = p^{−1/2}`. -/
def primeHalf (p : ℕ) : ℝ := (Real.sqrt p)⁻¹

section Vectors

variable {P : Finset ℕ}

/-- The frequency `λ(a) = Σ_p a_p log p`. -/
def vecFreq (a : P → ℤ) : ℝ := ∑ p : P, (a p : ℝ) * Real.log p

/-- The reduced numerator `Π_p p^{a_p⁺}`. -/
def vecNum (a : P → ℤ) : ℕ := ∏ p : P, (p : ℕ) ^ (a p).toNat

/-- The reduced denominator `Π_p p^{a_p⁻}`. -/
def vecDen (a : P → ℤ) : ℕ := ∏ p : P, (p : ℕ) ^ (-a p).toNat

variable (hP : ∀ p ∈ P, p.Prime)
include hP

theorem vecNum_pos (a : P → ℤ) : 0 < vecNum a :=
  Finset.prod_pos fun p _ => pow_pos (hP p p.2).pos _

theorem vecDen_pos (a : P → ℤ) : 0 < vecDen a :=
  Finset.prod_pos fun p _ => pow_pos (hP p p.2).pos _

theorem coprime_vecNum_vecDen (a : P → ℤ) : Nat.Coprime (vecNum a) (vecDen a) := by
  unfold vecNum vecDen
  refine Nat.Coprime.prod_left fun p _ => Nat.Coprime.prod_right fun q _ => ?_
  by_cases hpq : p = q
  · subst hpq
    rcases le_or_gt 0 (a p) with h | h
    · have e : (-a p).toNat = 0 := by omega
      rw [e, pow_zero]
      exact Nat.coprime_one_right _
    · have e : (a p).toNat = 0 := by omega
      rw [e, pow_zero]
      exact Nat.coprime_one_left _
  · exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hP p p.2) (hP q q.2)).mpr
      fun h => hpq (Subtype.ext h))

theorem vecFreq_eq (a : P → ℤ) :
    vecFreq a = Real.log (vecNum a) - Real.log (vecDen a) := by
  have hp0 : ∀ p : P, ((p : ℕ) : ℝ) ≠ 0 := fun p => by exact_mod_cast (hP p p.2).ne_zero
  unfold vecFreq vecNum vecDen
  push_cast
  rw [Real.log_prod (fun p _ => pow_ne_zero _ (hp0 p)),
    Real.log_prod (fun p _ => pow_ne_zero _ (hp0 p)), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Real.log_pow, Real.log_pow, ← sub_mul]
  congr 1
  have h := congrArg (Int.cast : ℤ → ℝ) (Int.toNat_sub_toNat_neg (a p))
  push_cast at h
  exact h.symm

omit hP in
theorem inv_sqrt_vecNum_mul_vecDen (a : P → ℤ) :
    (Real.sqrt ((vecNum a : ℝ) * vecDen a))⁻¹ = ∏ p : P, primeHalf p ^ (a p).natAbs := by
  have hprod : ((vecNum a : ℝ) * vecDen a) = (∏ p : P, Real.sqrt (p : ℕ) ^ (a p).natAbs) ^ 2 := by
    unfold vecNum vecDen
    push_cast
    rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_add, ← pow_mul, Int.toNat_add_toNat_neg_eq_natAbs, mul_comm, pow_mul,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [hprod, Real.sqrt_sq (Finset.prod_nonneg fun p _ => by positivity), ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [primeHalf, inv_pow]

end Vectors

/-! ## The Poisson cancellation -/

/-- The Fourier coefficients of `|1 − s e^{iθ}|²`: `1 + s²` at `0`, `−s` at `±1`. -/
def bohrCoeff (s : ℝ) (c : ℤ) : ℝ := if c = 0 then 1 + s ^ 2 else -s

/-- The three Fourier modes `{−1, 0, 1}`. -/
def bohrModes : Finset ℤ := {-1, 0, 1}

theorem sum_bohrModes {M : Type*} [AddCommMonoid M] (f : ℤ → M) :
    ∑ c ∈ bohrModes, f c = f (-1) + f 0 + f 1 := by
  unfold bohrModes
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    add_assoc]

/-- **Per-prime Poisson cancellation**: `(1 + s²) s^{|m|} − s(s^{|m−1|} + s^{|m+1|}) = (1 − s²)[m = 0]`. -/
theorem sum_bohrCoeff_mul_pow (s : ℝ) (m : ℤ) :
    ∑ c ∈ bohrModes, bohrCoeff s c * s ^ (m - c).natAbs = if m = 0 then 1 - s ^ 2 else 0 := by
  have b0 : bohrCoeff s 0 = 1 + s ^ 2 := if_pos rfl
  have b1 : bohrCoeff s 1 = -s := if_neg (by decide)
  have bm : bohrCoeff s (-1) = -s := if_neg (by decide)
  rw [sum_bohrModes, b0, b1, bm, sub_neg_eq_add, sub_zero]
  rcases lt_trichotomy m 0 with h | h | h
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, m = -((k : ℤ) + 1) := ⟨(-m - 1).toNat, by omega⟩
    subst hk
    rw [if_neg (show -((k : ℤ) + 1) ≠ 0 by omega)]
    have e1 : (-((k : ℤ) + 1) + 1).natAbs = k := by omega
    have e2 : (-((k : ℤ) + 1)).natAbs = k + 1 := by omega
    have e3 : (-((k : ℤ) + 1) - 1).natAbs = k + 2 := by omega
    rw [e1, e2, e3]
    ring
  · subst h
    simp
    ring
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, m = (k : ℤ) + 1 := ⟨(m - 1).toNat, by omega⟩
    subst hk
    rw [if_neg (show (k : ℤ) + 1 ≠ 0 by omega)]
    have e1 : ((k : ℤ) + 1 + 1).natAbs = k + 2 := by omega
    have e2 : ((k : ℤ) + 1).natAbs = k + 1 := by omega
    have e3 : ((k : ℤ) + 1 - 1).natAbs = k := by omega
    rw [e1, e2, e3]
    ring

/-- The Bohr coefficient of a mode vector: `E(c) = Π_p e_{c_p}(s_p)`. -/
def bohrVecCoeff {P : Finset ℕ} (s : P → ℝ) (c : P → ℤ) : ℝ := ∏ p : P, bohrCoeff (s p) (c p)

/-- **The Euler factors cancel the Bohr lift**:
`Σ_c E(c) Π_p s_p^{|a_p − c_p|} = Π_p (1 − s_p²) [a = 0]`. -/
theorem sum_bohrVec_mul_prod_pow {P : Finset ℕ} (s : P → ℝ) (a : P → ℤ) :
    ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
        bohrVecCoeff s c * ∏ p : P, s p ^ (a p - c p).natAbs =
      if a = 0 then ∏ p : P, (1 - s p ^ 2) else 0 := by
  classical
  have e : ∀ c : P → ℤ, bohrVecCoeff s c * ∏ p : P, s p ^ (a p - c p).natAbs =
      ∏ p : P, (bohrCoeff (s p) (c p) * s p ^ (a p - c p).natAbs) := fun c => by
    rw [bohrVecCoeff, ← Finset.prod_mul_distrib]
  simp_rw [e]
  rw [← Finset.prod_univ_sum (fun _ : P => bohrModes)
    (fun p c => bohrCoeff (s p) c * s p ^ (a p - c).natAbs)]
  simp_rw [sum_bohrCoeff_mul_pow]
  rw [Finset.prod_ite_zero]
  congr 1
  apply propext
  constructor
  · intro h
    funext p
    exact h p (Finset.mem_univ p)
  · intro h p _
    rw [h]
    rfl

/-! ## The Euler weight and the twisted weight -/

/-- **One Euler factor as a trigonometric polynomial**:
`|1 − s e^{iθ}|² = Σ_{c ∈ {−1,0,1}} e_c(s) e^{icθ}`. -/
theorem normSq_one_sub_mul_exp_eq_sum (s θ : ℝ) :
    ((Complex.normSq (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) : ℝ) : ℂ) =
      ∑ c ∈ bohrModes, (bohrCoeff s c : ℂ) * Complex.exp (((c * θ : ℝ) : ℂ) * I) := by
  rw [← Complex.mul_conj, sum_bohrModes]
  have b0 : bohrCoeff s 0 = 1 + s ^ 2 := if_pos rfl
  have b1 : bohrCoeff s 1 = -s := if_neg (by decide)
  have bm : bohrCoeff s (-1) = -s := if_neg (by decide)
  rw [b0, b1, bm]
  have hconj : (starRingEnd ℂ) (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) =
      1 - (s : ℂ) * Complex.exp (-((θ : ℂ) * I)) := by
    rw [map_sub, map_one, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    ring_nf
  rw [hconj]
  have hprod : Complex.exp ((θ : ℂ) * I) * Complex.exp (-((θ : ℂ) * I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  push_cast
  simp only [neg_one_mul, one_mul, zero_mul, Complex.exp_zero, mul_one]
  have e1 : Complex.exp (-(θ : ℂ) * I) = Complex.exp (-((θ : ℂ) * I)) := by ring_nf
  rw [e1]
  linear_combination (s : ℂ) ^ 2 * hprod

/-- The Euler weight `Π_{p∈P} |1 − p^{−1/2} e^{it log p}|²`. -/
def eulerWeight (P : Finset ℕ) (t : ℝ) : ℝ :=
  ∏ p : P, Complex.normSq (1 - (primeHalf p : ℂ) * Complex.exp (((t * Real.log p : ℝ) : ℂ) * I))

/-- The twist weight `|1 + ε e^{it log n₀}|²`. -/
def twistWeight (ε : ℝ) (n₀ : ℕ) (t : ℝ) : ℝ :=
  Complex.normSq (1 - ((-ε : ℝ) : ℂ) * Complex.exp (((t * Real.log n₀ : ℝ) : ℂ) * I))

/-- The notch weight `q(t) = |1 + ε n₀^{it}|² Π_p |1 − p^{−1/2+it}|²`. -/
def notchWeight (P : Finset ℕ) (ε : ℝ) (n₀ : ℕ) (t : ℝ) : ℝ := twistWeight ε n₀ t * eulerWeight P t

theorem notchWeight_nonneg (P : Finset ℕ) (ε : ℝ) (n₀ : ℕ) (t : ℝ) : 0 ≤ notchWeight P ε n₀ t :=
  mul_nonneg (Complex.normSq_nonneg _) (Finset.prod_nonneg fun _ _ => Complex.normSq_nonneg _)

/-- The frequency of a mode pair `(j, c)`: `j log n₀ + λ(c)`. -/
def modeFreq {P : Finset ℕ} (n₀ : ℕ) (j : ℤ) (c : P → ℤ) : ℝ := j * Real.log n₀ + vecFreq c

/-- The coefficient of a mode pair `(j, c)`: `e_j(−ε) E(c)`. -/
def modeCoeff {P : Finset ℕ} (ε : ℝ) (j : ℤ) (c : P → ℤ) : ℝ :=
  bohrCoeff (-ε) j * bohrVecCoeff (fun p : P => primeHalf p) c

/-- **The notch weight as a trigonometric polynomial.** -/
theorem notchWeight_eq_sum (P : Finset ℕ) (ε : ℝ) (n₀ : ℕ) (t : ℝ) :
    ((notchWeight P ε n₀ t : ℝ) : ℂ) =
      ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
        (modeCoeff ε j c : ℂ) * Complex.exp (((t * modeFreq n₀ j c : ℝ) : ℂ) * I) := by
  classical
  have htw : ((twistWeight ε n₀ t : ℝ) : ℂ) = ∑ j ∈ bohrModes, (bohrCoeff (-ε) j : ℂ) *
      Complex.exp (((j * (t * Real.log n₀) : ℝ) : ℂ) * I) :=
    normSq_one_sub_mul_exp_eq_sum (-ε) (t * Real.log n₀)
  have hew : ((eulerWeight P t : ℝ) : ℂ) = ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
      (bohrVecCoeff (fun p : P => primeHalf p) c : ℂ) *
        Complex.exp (((t * vecFreq c : ℝ) : ℂ) * I) := by
    unfold eulerWeight
    push_cast
    have hfac : ∀ p : P, ((Complex.normSq (1 - (primeHalf p : ℂ) *
        Complex.exp (((t * Real.log p : ℝ) : ℂ) * I)) : ℝ) : ℂ) =
        ∑ c ∈ bohrModes, (bohrCoeff (primeHalf p) c : ℂ) *
          Complex.exp (((c * (t * Real.log p) : ℝ) : ℂ) * I) :=
      fun p => normSq_one_sub_mul_exp_eq_sum _ _
    push_cast at hfac
    simp_rw [hfac]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum, bohrVecCoeff, vecFreq]
    push_cast
    congr 1
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  unfold notchWeight
  rw [Complex.ofReal_mul, htw, hew, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold modeCoeff modeFreq
  push_cast
  rw [mul_add, add_mul, Complex.exp_add]
  ring_nf

theorem contDiff_notchWeight (P : Finset ℕ) (ε : ℝ) (n₀ : ℕ) (n : WithTop ℕ∞) :
    ContDiff ℝ n fun t => ((notchWeight P ε n₀ t : ℝ) : ℂ) := by
  have e : (fun t => ((notchWeight P ε n₀ t : ℝ) : ℂ)) = fun t =>
      ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
        (modeCoeff ε j c : ℂ) * Complex.exp (((t * modeFreq n₀ j c : ℝ) : ℂ) * I) :=
    funext (notchWeight_eq_sum P ε n₀)
  rw [e]
  refine ContDiff.sum fun j _ => ContDiff.sum fun c _ => contDiff_const.mul ?_
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_id.mul contDiff_const)).mul
    contDiff_const).cexp

theorem exp_mul_exp_twist (t μ y : ℝ) :
    Complex.exp (((t * μ : ℝ) : ℂ) * I) * Complex.exp (-((y : ℂ) * t) * I) =
      Complex.exp (-(((y - μ : ℝ) : ℂ) * t) * I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The weighted moment is a finite combination of twisted moments.** -/
theorem weightedMoment_notchWeight_eq {L : ℝ} (hL : 0 < L) (P : Finset ℕ) (ε : ℝ) (n₀ : ℕ)
    (y : ℝ) :
    weightedMoment L (notchWeight P ε n₀) y =
      ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
        (modeCoeff ε j c : ℂ) * twistedMoment L (y - modeFreq n₀ j c) := by
  classical
  set F : ℤ → (P → ℤ) → ℝ → ℂ := fun j c t => (modeCoeff ε j c : ℂ) *
    (notchWindow L t * zetaSq t * Complex.exp (-(((y - modeFreq n₀ j c : ℝ) : ℂ) * t) * I))
    with hF
  have hFi : ∀ j c, Integrable (F j c) := fun j c =>
    (integrable_notchWindow_mul_continuous hL (f := fun t => zetaSq t *
      Complex.exp (-(((y - modeFreq n₀ j c : ℝ) : ℂ) * t) * I))
      ((contDiff_zetaSq 0).continuous.mul (by fun_prop))).const_mul _ |>.congr
      (Eventually.of_forall fun t => by simp only [hF]; ring)
  have hpt : ∀ t, notchWindow L t * ((notchWeight P ε n₀ t : ℝ) : ℂ) * zetaSq t *
      Complex.exp (-(y * t) * I) = ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
        F j c t := by
    intro t
    rw [notchWeight_eq_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hF]
    rw [← exp_mul_exp_twist t (modeFreq n₀ j c) y]
    ring
  unfold weightedMoment
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun c _ => hFi j c)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ (fun c _ => hFi j c)]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [hF]
  rw [integral_const_mul]
  rfl

/-! ## Exponent vectors of smooth numbers -/

/-- The exponent vector `(v_p(n))_{p∈P}`. -/
def vecOf (P : Finset ℕ) (n : ℕ) : P → ℤ := fun p => (n.factorization p : ℤ)

theorem vecFreq_vecOf {P : Finset ℕ} {n : ℕ} (hn : n.primeFactors ⊆ P) :
    vecFreq (vecOf P n) = Real.log n := by
  rw [log_eq_sum_factorization hn, ← Finset.sum_coe_sort P]
  unfold vecFreq vecOf
  push_cast
  rfl

theorem vecFreq_add {P : Finset ℕ} (a b : P → ℤ) : vecFreq (a + b) = vecFreq a + vecFreq b := by
  unfold vecFreq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.add_apply]
  push_cast
  ring

theorem vecFreq_sub {P : Finset ℕ} (a b : P → ℤ) : vecFreq (a - b) = vecFreq a - vecFreq b := by
  unfold vecFreq
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.sub_apply]
  push_cast
  ring

theorem vecFreq_smul {P : Finset ℕ} (j : ℤ) (a : P → ℤ) : vecFreq (j • a) = j * vecFreq a := by
  unfold vecFreq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem modeFreq_eq {P : Finset ℕ} {n₀ : ℕ} (hn₀ : n₀.primeFactors ⊆ P) (j : ℤ) (c : P → ℤ) :
    modeFreq n₀ j c = vecFreq (j • vecOf P n₀ + c) := by
  rw [vecFreq_add, vecFreq_smul, vecFreq_vecOf hn₀]
  rfl

theorem vecOf_nonneg (P : Finset ℕ) (n : ℕ) (p : P) : 0 ≤ vecOf P n p := Int.natCast_nonneg _

theorem vecOf_ne_zero {P : Finset ℕ} {n : ℕ} (hn : IsSmoothOver P n) : vecOf P n ≠ 0 := by
  intro h
  obtain ⟨q, hq⟩ := Nat.nonempty_primeFactors.mpr hn.1
  have hqP : q ∈ P := hn.2 hq
  have h1 := congrFun h ⟨q, hqP⟩
  simp only [vecOf, Pi.zero_apply, Nat.cast_eq_zero] at h1
  have hpos : 0 < n.factorization q :=
    (Nat.prime_of_mem_primeFactors hq).factorization_pos_of_dvd (by have := hn.1; omega)
      (Nat.dvd_of_mem_primeFactors hq)
  omega

theorem eq_of_vecOf_eq {P : Finset ℕ} {n m : ℕ} (hn : IsSmoothOver P n) (hm : IsSmoothOver P m)
    (h : vecOf P n = vecOf P m) : n = m := by
  refine Nat.eq_of_factorization_eq (by have := hn.1; omega) (by have := hm.1; omega) fun p => ?_
  by_cases hp : p ∈ P
  · have := congrFun h ⟨p, hp⟩
    simp only [vecOf, Nat.cast_inj] at this
    exact this
  · rw [factorization_eq_zero_of_notMem hn.2 hp, factorization_eq_zero_of_notMem hm.2 hp]

/-- The only resonance of the lifted diagonal among smooth twists is `n = n₀`, `j = 1`. -/
theorem vecOf_sub_smul_eq_zero_iff {P : Finset ℕ} {n n₀ : ℕ} (hn : IsSmoothOver P n)
    (hn₀ : IsSmoothOver P n₀) {j : ℤ} (hj : j ∈ bohrModes) :
    vecOf P n - j • vecOf P n₀ = 0 ↔ j = 1 ∧ n = n₀ := by
  constructor
  · intro h
    have h' : vecOf P n = j • vecOf P n₀ := sub_eq_zero.mp h
    unfold bohrModes at hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exfalso
      obtain ⟨q, hq⟩ := Nat.nonempty_primeFactors.mpr hn.1
      have hqP : q ∈ P := hn.2 hq
      have h1 := congrFun h' ⟨q, hqP⟩
      have hpos : 0 < n.factorization q :=
        (Nat.prime_of_mem_primeFactors hq).factorization_pos_of_dvd (by have := hn.1; omega)
          (Nat.dvd_of_mem_primeFactors hq)
      have h0 := vecOf_nonneg P n₀ ⟨q, hqP⟩
      simp only [vecOf, Pi.smul_apply, smul_eq_mul, neg_one_mul] at h1 h0
      omega
    · exact absurd (by rw [h', zero_smul]) (vecOf_ne_zero hn)
    · exact ⟨rfl, eq_of_vecOf_eq hn hn₀ (by rw [h', one_smul])⟩
  · rintro ⟨rfl, rfl⟩
    rw [one_smul, sub_self]

end RHTower.ZetaNotch
