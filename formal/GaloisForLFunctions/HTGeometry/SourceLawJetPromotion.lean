import GaloisForLFunctions.HTGeometry.PrimeBooleanMassHankelQuantumFusion

/-!
# Source-law jet promotion and withheld-organ reconstruction

A static polynomial relation ideal is only a ledger.  This module adds the generative operation:
source deformation prolongs a law to a Hasse response tower.  Product laws with an invertible
zeroth port reconstruct every withheld response recursively.  Algebra observers preserve source
laws, injective observers reflect them, and noninjective observers can create false closure.

The abstract mechanism is tested in two independent laboratories:

* a conservative visible/hidden split, whose hidden jet is reconstructed at every order;
* the finite Boolean incidence--Mass--Hankel--QFI packet, where differentiation of the exact
  four-organ volume law predicts the QFI response from the other three organs.
-/

namespace HTGeometry

noncomputable section

open Filter

/-! ## Static source laws and observer fracture -/

variable {R S T ι : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- Polynomial evaluation at a source-generated organ family. -/
def sourceLawEval (z : ι → S) : MvPolynomial ι R →ₐ[R] S :=
  MvPolynomial.aeval z

/-- Ideal of all polynomial laws true of the source-generated organ family. -/
def sourceLawIdeal (z : ι → S) : Ideal (MvPolynomial ι R) :=
  RingHom.ker (sourceLawEval z).toRingHom

/-- Evaluation after observation is observation after source evaluation. -/
theorem sourceLawEval_observer (φ : S →ₐ[R] T) (z : ι → S)
    (P : MvPolynomial ι R) :
    sourceLawEval (fun i => φ (z i)) P = φ (sourceLawEval z P) := by
  have h := congrArg (fun f : MvPolynomial ι R →ₐ[R] T => f P)
    (MvPolynomial.algHom_ext
      (f := sourceLawEval (fun i => φ (z i)))
      (g := φ.comp (sourceLawEval z)) (fun i => by simp [sourceLawEval]))
  simpa [sourceLawEval] using h

/-- Every source law remains a law after applying an algebra observer. -/
theorem sourceLawIdeal_le_observer (φ : S →ₐ[R] T) (z : ι → S) :
    sourceLawIdeal (R := R) z ≤ sourceLawIdeal (R := R) (fun i => φ (z i)) := by
  intro P hP
  rw [sourceLawIdeal, RingHom.mem_ker] at hP ⊢
  change sourceLawEval z P = 0 at hP
  change sourceLawEval (fun i => φ (z i)) P = 0
  rw [sourceLawEval_observer, hP, map_zero]

/-- An injective observer reflects every polynomial law, so it creates no false closure. -/
theorem sourceLawIdeal_eq_observer_of_injective (φ : S →ₐ[R] T)
    (hφ : Function.Injective φ) (z : ι → S) :
    sourceLawIdeal (R := R) (fun i => φ (z i)) = sourceLawIdeal (R := R) z := by
  apply le_antisymm
  · intro P hP
    rw [sourceLawIdeal, RingHom.mem_ker] at hP ⊢
    change sourceLawEval (fun i => φ (z i)) P = 0 at hP
    change sourceLawEval z P = 0
    apply hφ
    simpa [sourceLawEval_observer] using hP
  · exact sourceLawIdeal_le_observer φ z

/-- Every nontrivial kernel element gives a one-coordinate law created only by observation. -/
theorem observer_can_create_relation (φ : S →ₐ[R] T) (x : S)
    (hx : x ≠ 0) (hφx : φ x = 0) :
    (MvPolynomial.X () : MvPolynomial Unit R) ∉
        sourceLawIdeal (R := R) (fun _ : Unit => x) ∧
      (MvPolynomial.X () : MvPolynomial Unit R) ∈
        sourceLawIdeal (R := R) (fun _ : Unit => φ x) := by
  constructor
  · simp [sourceLawIdeal, sourceLawEval, hx]
  · simp [sourceLawIdeal, sourceLawEval, hφx]

/-! ## Hasse response towers -/

variable {K L : Type*} [CommRing K] [CommRing L]

/-- Cauchy product of divided/Hasse response jets. -/
def hasseJetMul (a b : ℕ → K) (n : ℕ) : K :=
  ∑ j ∈ Finset.range (n + 1), a j * b (n - j)

/-- The all-order prolongation of the product law `q * m = c * h`. -/
def IsProlongedProductLaw (c : K) (q m h : ℕ → K) : Prop :=
  ∀ n, hasseJetMul q m n = c * h n

/-- Ring maps commute with Hasse-jet multiplication. -/
theorem hasseJetMul_map (φ : K →+* L) (a b : ℕ → K) (n : ℕ) :
    φ (hasseJetMul a b n) = hasseJetMul (fun j => φ (a j)) (fun j => φ (b j)) n := by
  simp [hasseJetMul]

/-- Every prolonged product law transports through a change of coefficients. -/
theorem IsProlongedProductLaw.map (φ : K →+* L) {c : K} {q m h : ℕ → K}
    (hlaw : IsProlongedProductLaw c q m h) :
    IsProlongedProductLaw (φ c) (fun j => φ (q j)) (fun j => φ (m j))
      (fun j => φ (h j)) := by
  intro n
  rw [← hasseJetMul_map, hlaw n, map_mul]

/-- An injective coefficient observer reflects the complete prolonged law. -/
theorem isProlongedProductLaw_iff_map_of_injective (φ : K →+* L)
    (hφ : Function.Injective φ) (c : K) (q m h : ℕ → K) :
    IsProlongedProductLaw (φ c) (fun j => φ (q j)) (fun j => φ (m j))
        (fun j => φ (h j)) ↔ IsProlongedProductLaw c q m h := by
  constructor
  · intro hlaw n
    apply hφ
    rw [hasseJetMul_map, hlaw n, map_mul]
  · exact fun hlaw => hlaw.map φ

variable {F : Type*} [Field F]

/-- **All-order withheld-organ reconstruction.**  An invertible zeroth Mass port makes the
prolonged fusion law triangular and reconstructs response `q n`. -/
theorem prolongedProductLaw_reconstruct {c : F} {q m h : ℕ → F}
    (hlaw : IsProlongedProductLaw c q m h) (hm0 : m 0 ≠ 0) (n : ℕ) :
    q n = (c * h n - ∑ j ∈ Finset.range n, q j * m (n - j)) / m 0 := by
  have hn := hlaw n
  rw [hasseJetMul, Finset.sum_range_succ] at hn
  simp only [Nat.sub_self] at hn
  apply (eq_div_iff hm0).2
  linear_combination hn

/-- Zeroth-order member of a prolonged product law. -/
theorem prolongedProductLaw_zero {c : F} {q m h : ℕ → F}
    (hlaw : IsProlongedProductLaw c q m h) :
    q 0 * m 0 = c * h 0 := by
  simpa [hasseJetMul] using hlaw 0

/-- First promoted member of a prolonged product law. -/
theorem prolongedProductLaw_first {c : F} {q m h : ℕ → F}
    (hlaw : IsProlongedProductLaw c q m h) :
    q 1 * m 0 + q 0 * m 1 = c * h 1 := by
  have h := hlaw 1
  rw [hasseJetMul, Finset.sum_range_succ, Finset.sum_range_succ] at h
  simp at h
  linear_combination h

/-- The complete withheld response jet is unique once the zeroth multiplier port is nonzero. -/
theorem prolongedProductLaw_unique {c : F} {q q' m h : ℕ → F}
    (hlaw : IsProlongedProductLaw c q m h)
    (hlaw' : IsProlongedProductLaw c q' m h) (hm0 : m 0 ≠ 0) :
    q = q' := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [prolongedProductLaw_reconstruct hlaw hm0 n,
        prolongedProductLaw_reconstruct hlaw' hm0 n]
      congr 2
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih j (Finset.mem_range.mp hj)]

/-! ## Passive split laboratory -/

/-- First response of `a^2 + d^2 = 1`: visible response predicts hidden response. -/
theorem passiveSplit_firstResponse {a0 a1 d0 d1 : F}
    (h : a0 * a1 + d0 * d1 = 0) (hd0 : d0 ≠ 0) :
    d1 = -(a0 / d0) * a1 := by
  calc
    d1 = -(a0 * a1) / d0 := (eq_div_iff hd0).2 (by linear_combination h)
    _ = -(a0 / d0) * a1 := by field_simp

/-- Hasse jet of the constant function one. -/
def hasseJetUnit : ℕ → F
  | 0 => 1
  | _ + 1 => 0

/-- Complete conservative split law `a^2 + d^2 = 1` in Hasse coordinates. -/
def IsPassiveSplitLaw (a d : ℕ → F) : Prop :=
  ∀ n, hasseJetMul a a n + hasseJetMul d d n = hasseJetUnit n

/-- The interior terms of the Hasse coefficient of a square. -/
def hasseJetSquareMiddle (d : ℕ → F) (n : ℕ) : F :=
  ∑ j ∈ Finset.range n, d (j + 1) * d (n - j)

/-- Endpoint/interior decomposition of the next Hasse coefficient of a square. -/
theorem hasseJetMul_self_succ (d : ℕ → F) (n : ℕ) :
    hasseJetMul d d (n + 1) =
      2 * d 0 * d (n + 1) + hasseJetSquareMiddle d n := by
  have hmiddle :
      (∑ j ∈ Finset.range n, d (j + 1) * d ((n + 1) - (j + 1))) =
        hasseJetSquareMiddle d n := by
    unfold hasseJetSquareMiddle
    apply Finset.sum_congr rfl
    intro j hj
    rw [show (n + 1) - (j + 1) = n - j by omega]
  rw [hasseJetMul, Finset.sum_range_succ, Finset.sum_range_succ']
  rw [hmiddle]
  simp only [Nat.sub_zero, Nat.sub_self]
  ring

/-- **All-order passive-history prediction.**  If `2` and the initial hidden amplitude are
nonzero, visible jets and earlier hidden jets reconstruct the next hidden response. -/
theorem passiveSplitLaw_reconstruct {a d : ℕ → F}
    (hlaw : IsPassiveSplitLaw a d) (h2 : (2 : F) ≠ 0) (hd0 : d 0 ≠ 0) (n : ℕ) :
    d (n + 1) =
      -(2 * a 0 * a (n + 1) + hasseJetSquareMiddle a n + hasseJetSquareMiddle d n) /
        (2 * d 0) := by
  have h := hlaw (n + 1)
  rw [hasseJetMul_self_succ, hasseJetMul_self_succ] at h
  simp [hasseJetUnit] at h
  apply (eq_div_iff (mul_ne_zero h2 hd0)).2
  linear_combination h

/-! ## Boolean--Mass--Hankel--QFI laboratory -/

open ConstraintFrameRelativity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Mass energy along the exact finite Boolean tilt. -/
def booleanTiltMassEnergy (q lam : ι → ℝ) (r : Finset ι → ℝ) (e : ℝ) : ℝ :=
  tiltCov (bernoulliWeight q) r e (linearStat lam) (linearStat lam)

/-- First Hankel determinant along the exact finite Boolean tilt. -/
def booleanTiltHankelDet (q lam : ι → ℝ) (r : Finset ι → ℝ) (e : ℝ) : ℝ :=
  tiltCov (bernoulliWeight q) r e (linearStat fun _ => 1) (linearStat fun _ => 1) *
      tiltCov (bernoulliWeight q) r e (linearStat lam) (linearStat lam) -
    tiltCov (bernoulliWeight q) r e (linearStat fun _ => 1) (linearStat lam) *
      tiltCov (bernoulliWeight q) r e (linearStat fun _ => 1) (linearStat lam)

/-- Exact first response of tilted Mass energy. -/
def booleanTiltMassResponse (q lam : ι → ℝ) (r : Finset ι → ℝ) : ℝ :=
  wcov (bernoulliWeight q) r (fun S =>
    (linearStat lam S - wexp (bernoulliWeight q) (linearStat lam)) *
      (linearStat lam S - wexp (bernoulliWeight q) (linearStat lam)))

/-- Exact first response of the tilted Hankel determinant. -/
def booleanTiltHankelResponse (q lam : ι → ℝ) (r : Finset ι → ℝ) : ℝ :=
  let μ := bernoulliWeight q
  let f := linearStat fun _ : ι => 1
  let g := linearStat lam
  let a1 := wcov μ r (fun S => (f S - wexp μ f) * (f S - wexp μ f))
  let b1 := wcov μ r (fun S => (f S - wexp μ f) * (g S - wexp μ g))
  let c1 := wcov μ r (fun S => (g S - wexp μ g) * (g S - wexp μ g))
  a1 * wcov μ g g + wcov μ f f * c1 - 2 * wcov μ f g * b1

/-- Independently certified QFI response, named as the withheld fourth-organ coordinate. -/
def booleanTiltQFIResponse (q lam : ι → ℝ) (r : Finset ι → ℝ) : ℝ :=
  4 * (Real.pi ^ 2 * wcov (bernoulliWeight q) r (fun S =>
    ((linearStat (fun _ => 1) S - wexp (bernoulliWeight q) (linearStat fun _ => 1))
      - (capB (bernoulliVar q) lam / capC (bernoulliVar q) lam)
        * (linearStat lam S - wexp (bernoulliWeight q) (linearStat lam))) ^ 2))

/-- Zeroth tilted Mass coordinate is the existing fusion Mass organ. -/
theorem booleanTiltMassEnergy_zero (q lam : ι → ℝ) (r : Finset ι → ℝ) :
    booleanTiltMassEnergy q lam r 0 = fusionMassEnergy (bernoulliVar q) lam := by
  rw [booleanTiltMassEnergy, tiltCov_zero (sum_bernoulliWeight q), fusionMassEnergy,
    wcov_bernoulliWeight, bernoulliCov_lam_lam]

/-- Zeroth tilted determinant is the existing fusion Hankel organ. -/
theorem booleanTiltHankelDet_zero (q lam : ι → ℝ) (r : Finset ι → ℝ) :
    booleanTiltHankelDet q lam r 0 = fusionHankelDet (bernoulliVar q) lam := by
  rw [booleanTiltHankelDet, tiltCov_zero (sum_bernoulliWeight q),
    tiltCov_zero (sum_bernoulliWeight q), tiltCov_zero (sum_bernoulliWeight q),
    fusionHankelDet,
    wcov_bernoulliWeight q (linearStat fun _ => 1) (linearStat fun _ => 1),
    wcov_bernoulliWeight q (linearStat fun _ => 1) (linearStat lam),
    wcov_bernoulliWeight q (linearStat lam) (linearStat lam),
    bernoulliCov_one_one, bernoulliCov_one_lam, bernoulliCov_lam_lam, pow_two]

/-- Zeroth tilted QFI coordinate is the existing transverse-QFI fusion organ. -/
theorem booleanTiltTransverseQFI_zero (q lam : ι → ℝ) (r : Finset ι → ℝ) :
    booleanTiltTransverseQFI q lam r 0 = fusionTransverseQFI (bernoulliVar q) lam := by
  rw [booleanTiltTransverseQFI, tiltCov_zero (sum_bernoulliWeight q),
    tiltCov_zero (sum_bernoulliWeight q), tiltCov_zero (sum_bernoulliWeight q),
    fusionTransverseQFI, schurCapacity,
    wcov_bernoulliWeight q (linearStat fun _ => 1) (linearStat fun _ => 1),
    wcov_bernoulliWeight q (linearStat fun _ => 1) (linearStat lam),
    wcov_bernoulliWeight q (linearStat lam) (linearStat lam),
    bernoulliCov_one_one, bernoulliCov_one_lam, bernoulliCov_lam_lam]

/-- The named Mass response is the derivative of tilted Mass energy. -/
theorem hasDerivAt_booleanTiltMassEnergy (q lam : ι → ℝ) (r : Finset ι → ℝ) :
    HasDerivAt (booleanTiltMassEnergy q lam r) (booleanTiltMassResponse q lam r) 0 := by
  change HasDerivAt
    (fun e => tiltCov (bernoulliWeight q) r e (linearStat lam) (linearStat lam))
    (booleanTiltMassResponse q lam r) 0
  exact hasDerivAt_tiltCov (sum_bernoulliWeight q) r (linearStat lam) (linearStat lam)

/-- The named Hankel response is the derivative of the tilted determinant. -/
theorem hasDerivAt_booleanTiltHankelDet (q lam : ι → ℝ) (r : Finset ι → ℝ) :
    HasDerivAt (booleanTiltHankelDet q lam r) (booleanTiltHankelResponse q lam r) 0 := by
  let μ := bernoulliWeight q
  let f := linearStat fun _ : ι => 1
  let g := linearStat lam
  have hA := hasDerivAt_tiltCov (sum_bernoulliWeight q) r f f
  have hB := hasDerivAt_tiltCov (sum_bernoulliWeight q) r f g
  have hC := hasDerivAt_tiltCov (sum_bernoulliWeight q) r g g
  have h := (hA.mul hC).sub (hB.mul hB)
  rw [tiltCov_zero (sum_bernoulliWeight q), tiltCov_zero (sum_bernoulliWeight q),
    tiltCov_zero (sum_bernoulliWeight q)] at h
  change HasDerivAt
    (fun e => tiltCov (bernoulliWeight q) r e f f *
        tiltCov (bernoulliWeight q) r e g g -
      tiltCov (bernoulliWeight q) r e f g * tiltCov (bernoulliWeight q) r e f g)
    (booleanTiltHankelResponse q lam r) 0
  exact h.congr_deriv (by simp [booleanTiltHankelResponse, f, g]; ring)

/-- The named fourth-organ response agrees with the independently certified QFI derivative. -/
theorem hasDerivAt_booleanTiltQFIResponse (q lam : ι → ℝ) (r : Finset ι → ℝ)
    (hC : capC (bernoulliVar q) lam ≠ 0) :
    HasDerivAt (booleanTiltTransverseQFI q lam r) (booleanTiltQFIResponse q lam r) 0 := by
  simpa [booleanTiltQFIResponse] using hasDerivAt_booleanTiltTransverseQFI q lam r hC

/-- The four-organ conserved-volume law holds at every tilted point with nonzero Mass port. -/
theorem booleanTilt_fusion_identity (q lam : ι → ℝ) (r : Finset ι → ℝ) (e : ℝ)
    (hM : booleanTiltMassEnergy q lam r e ≠ 0) :
    booleanTiltTransverseQFI q lam r e * booleanTiltMassEnergy q lam r e =
      4 * Real.pi ^ 2 * booleanTiltHankelDet q lam r e := by
  unfold booleanTiltTransverseQFI booleanTiltMassEnergy booleanTiltHankelDet at *
  field_simp

/-- **Four-organ first-response conservation.**  Incidence, Mass, and Hankel response force the
withheld QFI response; this agrees with the independently certified residual-covariance formula. -/
theorem booleanTilt_fourOrgan_firstResponse_conservation
    (q lam : ι → ℝ) (r : Finset ι → ℝ)
    (hC : capC (bernoulliVar q) lam ≠ 0) :
    booleanTiltQFIResponse q lam r * fusionMassEnergy (bernoulliVar q) lam +
        fusionTransverseQFI (bernoulliVar q) lam * booleanTiltMassResponse q lam r =
      4 * Real.pi ^ 2 * booleanTiltHankelResponse q lam r := by
  have hQ := hasDerivAt_booleanTiltQFIResponse q lam r hC
  have hM := hasDerivAt_booleanTiltMassEnergy q lam r
  have hH := hasDerivAt_booleanTiltHankelDet q lam r
  have hM0 : booleanTiltMassEnergy q lam r 0 ≠ 0 := by
    rw [booleanTiltMassEnergy_zero]
    exact hC
  have hne : ∀ᶠ e in nhds (0 : ℝ), booleanTiltMassEnergy q lam r e ≠ 0 :=
    hM.continuousAt.eventually_ne hM0
  have hrel :
      (fun e => booleanTiltTransverseQFI q lam r e * booleanTiltMassEnergy q lam r e)
        =ᶠ[nhds (0 : ℝ)]
      (fun e => 4 * Real.pi ^ 2 * booleanTiltHankelDet q lam r e) :=
    hne.mono fun e he => booleanTilt_fusion_identity q lam r e he
  have hleft := hQ.mul hM
  have hright := hH.const_mul (4 * Real.pi ^ 2)
  have hderiv :
      booleanTiltQFIResponse q lam r * booleanTiltMassEnergy q lam r 0 +
          booleanTiltTransverseQFI q lam r 0 * booleanTiltMassResponse q lam r =
        4 * Real.pi ^ 2 * booleanTiltHankelResponse q lam r :=
    hleft.unique (hright.congr_of_eventuallyEq hrel)
  rw [booleanTiltMassEnergy_zero, booleanTiltTransverseQFI_zero] at hderiv
  exact hderiv

end

end HTGeometry
