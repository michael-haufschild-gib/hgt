import GaloisForLFunctions.CountingHolography.Sections.ThePositiveInverseOfTheTwoPoleFilter
import GaloisForLFunctions.CountingHolography.Sections.TwoPoleFreeIntegerTranslates
import GaloisForLFunctions.CountingHolography.Sections.TheJetRadiusOfPoleBalancedSections

/-!
# Prime section comparisons with both pole degrees zero

At each prime and each integral log-four shift, a sum of two translates of
the same three-graph divisor realizes the corresponding filtered trace.
The ordinary-prime comparison for these divisors detects the critical line.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology ArithmeticScatteringHolography RenormalizedIntersectionTheory
open Zeta23 ArithmeticOrientationGeometry

private def label {N : ℕ} (x : ℕ) (hx : x < N) : Fin N := ⟨x-1,by omega⟩

private theorem label_degree {N x : ℕ} (hx : x < N) (h : 0 < x) :
    ((label x hx : Fin N):ℝ)+1 = x := by
  change ((x-1:ℕ):ℝ)+1=x
  rw [Nat.cast_sub h,Nat.cast_one,sub_add_cancel]

/-- Integral translate of the two-pole-free atom to conductors p, 4p and 16p. -/
def translatedTwoPole {N : ℕ} (p : ℕ) (hp : 16*p < N) : Fin N → ℤ :=
  threeGraphDivisor (label p (by omega)) (label (4*p) (by omega)) (label (16*p) hp) 2 (-5) (-2)

private theorem eval_translate {N p : ℕ} (hp : 16*p < N) (hpp : 0 < p) (F : ℝ → ℝ) :
    ∑ i : Fin N, F ((i:ℝ)+1)*(translatedTwoPole p hp i:ℝ) = 2*F p-5*F (4*p)+2*F (16*p) := by
  unfold translatedTwoPole
  rw [sum_threeGraphDivisor (fun i => F ((i:ℝ)+1)),label_degree _ hpp,
    label_degree _ (Nat.mul_pos (by decide) hpp),label_degree _ (Nat.mul_pos (by decide) hpp)]
  push_cast
  ring

/-- The actual integer graph presentation has the fixed index-detecting
spline as its source, translated by the logarithm of the carrier. -/
theorem splineSource_translatedTwoPole {N p : ℕ} (hp : 16*p < N) (hpp : 0 < p) (u : ℝ) :
    splineSource (translatedTwoPole p hp) u = twoPoleAtom (u-Real.log p) := by
  let B := BiScaleUncertainty.ChebyshevGauge.cubicSpline
  let F := fun z : ℝ => B (u-Real.log z)
  let G := fun i : Fin 16 => B (u-Real.log p-Real.log ((i:ℝ)+1))
  have hl : splineSource (translatedTwoPole p hp) u = ∑ i : Fin N, F ((i:ℝ)+1)*(translatedTwoPole p hp i:ℝ) :=
    sum_congr rfl fun i _ => mul_comm _ _
  have hr : twoPoleAtom (u-Real.log p) = ∑ i : Fin 16, G i*(twoPoleDivisor i:ℝ) :=
    sum_congr rfl fun i _ => mul_comm _ _
  rw [hl,hr,eval_translate hp hpp F,twoPoleDivisor,sum_threeGraphDivisor]
  have h₀ : ((0 : Fin 16):ℝ)+1 = 1 := by norm_num
  have h₃ : ((3 : Fin 16):ℝ)+1 = 4 := by change ((3:ℕ):ℝ)+1 = 4; norm_num
  have h₁₅ : ((15 : Fin 16):ℝ)+1 = 16 := by change ((15:ℕ):ℝ)+1 = 16; norm_num
  simp only [F,G,h₀,h₃,h₁₅,Real.log_one,sub_zero,Int.cast_ofNat,Int.cast_neg,
    Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (Nat.cast_pos.mpr hpp).ne',
    Real.log_mul (by norm_num : (16:ℝ) ≠ 0) (Nat.cast_pos.mpr hpp).ne',
    show u-(Real.log 4+Real.log p) = u-Real.log p-Real.log 4 by ring,
    show u-(Real.log 16+Real.log p) = u-Real.log p-Real.log 16 by ring]
  ring

theorem translatedTwoPole_degrees {N p : ℕ} (hp : 16*p < N) (hpp : 0 < p) :
    positivePoleDegree (translatedTwoPole p hp) = 0 ∧ negativePoleDegree (translatedTwoPole p hp) = 0 := by
  unfold positivePoleDegree negativePoleDegree
  rw [eval_translate hp hpp Real.sqrt,eval_translate hp hpp (fun x => (Real.sqrt x)⁻¹),
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 16)]
  norm_num [mul_inv_rev] <;> ring

/-- Sum of two integral translates, with at most eighteen units of total variation. -/
def twoPolePair (p q : ℕ) : Fin (16*(p+q)+1) → ℤ :=
  translatedTwoPole p (by omega) + translatedTwoPole q (by omega)

theorem twoPolePair_degrees {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    positivePoleDegree (twoPolePair p q) = 0 ∧ negativePoleDegree (twoPolePair p q) = 0 := by
  let N := 16*(p+q)+1
  have h₁ := translatedTwoPole_degrees (N := N) (by dsimp [N]; omega) hp
  have h₂ := translatedTwoPole_degrees (N := N) (by dsimp [N]; omega) hq
  simp only [twoPolePair,positivePoleDegree,negativePoleDegree] at h₁ h₂ ⊢
  simp only [Pi.add_apply,Int.cast_add,mul_add,sum_add_distrib,h₁.1,h₁.2,h₂.1,h₂.2,zero_add,and_self]

theorem twoPolePair_mass (p q : ℕ) : ∑ i, |(twoPolePair p q i:ℝ)| ≤ 18 := by
  let N := 16*(p+q)+1
  have h {r : ℕ} (hr : 16*r < N) : ∑ i, |(translatedTwoPole r hr i:ℝ)| ≤ 9 :=
    (threeGraphDivisor_mass _ _ _ _ _ _).trans (by norm_num)
  let a := translatedTwoPole p (N := N) (by dsimp [N]; omega)
  let b := translatedTwoPole q (N := N) (by dsimp [N]; omega)
  calc _ ≤ ∑ i, (|(a i:ℝ)|+|(b i:ℝ)|) := sum_le_sum fun i _ => by
             change |((a i+b i:ℤ):ℝ)| ≤ _
             rw [Int.cast_add]
             exact abs_add_le _ _
    _ ≤ 18 := by
             rw [sum_add_distrib]
             exact (add_le_add (h (r := p) (by dsimp [N]; omega)) (h (r := q) (by dsimp [N]; omega))).trans (by norm_num)

private def pairing {N : ℕ} (a b : Fin N → ℤ) :=
  ∑ i, ∑ j, (atomGram N i j).re*(a i:ℝ)*(b j:ℝ)

private theorem translated_pairing {N p q : ℕ} (hp : 16*p < N) (hq : 16*q < N)
    (hp' : 0 < p) (hq' : 0 < q) :
    pairing (translatedTwoPole p hp) (translatedTwoPole q hq) = twoPoleTrace (Real.log p-Real.log q) := by
  let a := translatedTwoPole p hp
  let b := translatedTwoPole q hq
  let R (x : ℝ) := 2*realSplineTrace (Real.log x-Real.log q)-
    5*realSplineTrace (Real.log x-Real.log (4*q))+2*realSplineTrace (Real.log x-Real.log (16*q))
  have row (i : Fin N) : (∑ j, (atomGram N i j).re*(a i:ℝ)*(b j:ℝ)) = R ((i:ℝ)+1)*(a i:ℝ) := by
    let F := fun z : ℝ => realSplineTrace (Real.log ((i:ℝ)+1)-Real.log z)
    have he : R ((i:ℝ)+1) = ∑ j : Fin N, F ((j:ℝ)+1)*(b j:ℝ) := (eval_translate hq hq' F).symm
    rw [he,sum_mul]
    exact sum_congr rfl fun j _ => by rw [atomGram_eq_splineSeries]; unfold F realSplineTrace; ring
  change (∑ i, ∑ j, (atomGram N i j).re*(a i:ℝ)*(b j:ℝ)) = _
  simp_rw [row]
  rw [eval_translate hp hp' R]
  have hl : Real.log 16 = 2*Real.log 4 := by
    rw [show (16:ℝ) = 4^2 by norm_num,Real.log_pow]; norm_num
  simp only [R,twoPoleTrace,Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (Nat.cast_pos.mpr hp').ne',
    Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (Nat.cast_pos.mpr hq').ne',
    Real.log_mul (by norm_num : (16:ℝ) ≠ 0) (Nat.cast_pos.mpr hp').ne',
    Real.log_mul (by norm_num : (16:ℝ) ≠ 0) (Nat.cast_pos.mpr hq').ne',hl]
  ring_nf

private theorem pairing_comm {N : ℕ} (a b : Fin N → ℤ) : pairing a b = pairing b a := by
  unfold pairing
  rw [sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  have h : starRingEnd ℂ (atomGram N i j) = atomGram N j i :=
    congr_fun (congr_fun (atomGram_isHermitian N) j) i
  have hs := congrArg Complex.re h
  rw [← hs,Complex.conj_re]
  ring

/-- The full self-pairing is a constant diagonal and twice one filtered lag. -/
theorem integerProbe_twoPolePair {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    integerProbe _ (twoPolePair p q) = 2*twoPoleTrace 0+2*twoPoleTrace (Real.log p-Real.log q) := by
  let N := 16*(p+q)+1
  have hp' : 16*p < N := by dsimp [N]; omega
  have hq' : 16*q < N := by dsimp [N]; omega
  let a := translatedTwoPole p hp'
  let b := translatedTwoPole q hq'
  have he : integerProbe N (a+b) = pairing a a+pairing a b+(pairing b a+pairing b b) := by
    rw [integerProbe_eq_sum]
    simp only [pairing,Pi.add_apply,Int.cast_add,mul_add,add_mul,sum_add_distrib]
    ring
  change integerProbe N (a+b) = _
  rw [he,pairing_comm b a,translated_pairing hp' hp' hp hp,translated_pairing hq' hq' hq hq,
    translated_pairing hp' hq' hp hq,sub_self,sub_self]
  ring

/-- Conductors realizing the log-four orbit of one prime. -/
def primeOrbitConductors (p : ℕ) : ℤ → ℕ × ℕ
  | .ofNat k => (p*4^k,1)
  | .negSucc k => (p,4^(k+1))

private theorem primeOrbitConductors_spec {p : ℕ} (hp : p.Prime) (j : ℤ) :
    let c := primeOrbitConductors p j
    0 < c.1 ∧ 0 < c.2 ∧ Real.log c.1-Real.log c.2 = Real.log p+j*Real.log 4 := by
  have hp' := hp.pos
  cases j with
  | ofNat k =>
    refine ⟨Nat.mul_pos hp' (pow_pos (by decide) _),one_pos,?_⟩
    change Real.log ((p*4^k:ℕ):ℝ)-Real.log 1 = _
    push_cast
    rw [Real.log_mul (Nat.cast_pos.mpr hp').ne' (pow_pos (by norm_num : (0:ℝ)<4) _).ne',
      Real.log_pow,Real.log_one,sub_zero]
    norm_num
  | negSucc k =>
    refine ⟨hp',pow_pos (by decide) _,?_⟩
    change Real.log p-Real.log ((4^(k+1):ℕ):ℝ) = _
    push_cast
    rw [Real.log_pow]
    push_cast
    ring

/-- Both poles vanish on every divisor in this one-sided prime section criterion. -/
theorem riemannHypothesis_iff_twoPolePair_power :
    RiemannHypothesis ↔ ∃ B : ℕ, 0 < B ∧ ∀ p : ℕ, p.Prime → ∀ j : ℤ,
      let c := primeOrbitConductors p j
      ∃ᶠ m : ℕ in atTop, ordinaryPrimeGenerator (m • twoPolePair c.1 c.2) ≤ (B:ℚ)^(m^2) := by
  obtain ⟨C,hC,h⟩ := poleBalanced_ordinary_error
  let D := 324*C+4
  have herr {p q : ℕ} (hp : 0 < p) (hq : 0 < q) : ∀ᶠ m : ℕ in atTop,
      |Real.log (ordinaryPrimeGenerator (m • twoPolePair p q) : ℝ)+
        integerProbe _ (twoPolePair p q)*(m:ℝ)^2| ≤ D*(m:ℝ)^2 := by
    have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (sum_nonneg fun _ _ => abs_nonneg _) (twoPolePair_mass p q) 2) hC
    apply (h _ _ (twoPolePair_degrees hp hq).1).mono
    intro m he
    exact he.trans (mul_le_mul_of_nonneg_right (by dsimp only [D]; linarith only [hm]) (sq_nonneg _))
  constructor
  · intro hRH
    let B := ⌈Real.exp D⌉₊
    have hB : 0 < B := Nat.ceil_pos.mpr (Real.exp_pos _)
    have hl := (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hB)).mpr (Nat.le_ceil (Real.exp D))
    refine ⟨B,hB,fun p hp j => ?_⟩
    let c := primeOrbitConductors p j
    obtain ⟨h₁,h₂,_⟩ := primeOrbitConductors_spec hp j
    apply ((herr h₁ h₂).mono fun m hm => ?_).frequently
    have he := generator_le_power_iff (m • twoPolePair c.1 c.2) hB 1 m
    simp only [one_mul,Nat.cast_one,one_pow,mul_one] at he
    exact he.mpr (by linarith only [(abs_le.mp hm).2,mul_le_mul_of_nonneg_right hl (sq_nonneg (m:ℝ)),
      mul_nonneg (riemannHypothesis_iff_integerProbes.mp hRH _ (twoPolePair c.1 c.2)) (sq_nonneg (m:ℝ))])
  · rintro ⟨B,hB,hb⟩
    apply riemannHypothesis_iff_twoPoleTrace_prime_orbits.mpr
    refine ⟨(-Real.log B-D)/2-twoPoleTrace 0,fun p hp j => ?_⟩
    let c := primeOrbitConductors p j
    obtain ⟨h₁,h₂,he⟩ := primeOrbitConductors_spec hp j
    obtain ⟨m,hm,herr',hm'⟩ := ((hb p hp j).and_eventually ((herr h₁ h₂).and (eventually_ge_atTop 1))).exists
    have hb' := generator_le_power_iff (m • twoPolePair c.1 c.2) hB 1 m
    simp only [one_mul,Nat.cast_one,one_pow,mul_one] at hb'
    have hq : -Real.log B-D ≤ integerProbe _ (twoPolePair c.1 c.2) := by
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos (Nat.cast_pos.mpr hm' : (0:ℝ) < m))).mp
      linarith only [(abs_le.mp herr').1,hb'.mp hm]
    rw [integerProbe_twoPolePair h₁ h₂,he] at hq
    linarith only [hq]

#print axioms riemannHypothesis_iff_twoPolePair_power
#print axioms twoPolePair_degrees
#print axioms integerProbe_twoPolePair

end GaloisForLFunctions.CountingHolography.Sections
