import GaloisForLFunctions.RHTower.XiShiftEulerRationalShiftWitness
import GaloisForLFunctions.RHTower.PrimeWinningFaceAugmentation
import GaloisForLFunctions.RHTower.XiShiftEulerProductBridge
import GaloisForLFunctions.RHTower.FiniteEulerLocalQuartet
import GaloisForLFunctions.RHTower.XiShiftEulerDenseFiniteSection

/-!
# Finite prime-side certificates for shifted-Xi negative inertia

Finite products of the literal local Euler factors converge to the shifted completed-Xi quotient
throughout the Euler sampling region.  Hence every finite kernel energy converges to its exact
all-prime value.  Strict negative energy therefore has a finite-prime approximation with a positive
rational margin and a rigorously bounded all-prime tail.

Combining this stability theorem with rational shift avoidance and Gaussian-rational node locality
gives a closed arithmetic certificate theorem: RH fails exactly when such a finite prime packet,
rational shift, rational-node coefficient packet, and rational tail margin exist.  The certificate
predicate contains no zero or divisor witness.
-/

open Complex Set Topology Filter
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

private theorem tendsto_finset_sum_complex {A X : Type*}
    {l : Filter A} (s : Finset X) (f : X → A → ℂ) (g : X → ℂ)
    (h : ∀ x ∈ s, Tendsto (f x) l (nhds (g x))) :
    Tendsto (fun a => ∑ x ∈ s, f x a) l (nhds (∑ x ∈ s, g x)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (tendsto_const_nhds : Tendsto (fun _ : A => (0 : ℂ)) l (nhds 0))
  | @insert x s hx ih =>
      simp only [Finset.sum_insert hx]
      exact (h x (by simp)).add (ih (fun y hy => h y (by simp [hy])))

/-- Finite prime approximation to the shifted completed-Xi quotient. -/
def eulerXiShiftFinitePrimeTheta
    (omega : ℝ) (S : Finset Nat.Primes) (z : ℂ) : ℂ :=
  eulerXiArchimedeanQuotient omega z *
    ∏ p ∈ S, eulerXiPrimeShiftFactor p omega z

/-- The literal shifted local Euler factors multiply to the zeta quotient on the Euler sampling
region. -/
theorem eulerXiPrimeShiftFactor_hasProd
    {omega : ℝ} (homega : 0 < omega)
    {z : ℂ} (hz : z ∈ xiShiftEulerUpperSet omega) :
    HasProd (fun p : Nat.Primes => eulerXiPrimeShiftFactor p omega z)
      (riemannZeta (1 / 2 - (omega : ℂ) - z * I) /
        riemannZeta (1 / 2 + (omega : ℂ) - z * I)) := by
  have hm : 1 < (1 / 2 - (omega : ℂ) - z * I).re := by
    change 1 / 2 + omega < z.im at hz
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re, Complex.one_im,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    norm_num
    linarith
  have hp : 1 < (1 / 2 + (omega : ℂ) - z * I).re := by
    change 1 / 2 + omega < z.im at hz
    simp only [Complex.sub_re, Complex.add_re, Complex.div_re, Complex.one_re,
      Complex.one_im, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    norm_num
    linarith
  have hnum := hasProd_one_sub_primeCpow_neg hp
  have hden := riemannZeta_eulerProduct_hasProd hm
  have hprod := hnum.mul hden
  convert hprod using 1
  · funext p
    rw [eulerXiPrimeShiftFactor, finiteEulerLocalFactor_eq_one_sub_natCast_cpow,
      finiteEulerLocalFactor_eq_one_sub_natCast_cpow]
    ring
  · ring

/-- Finite prime approximations converge to the exact completed-Xi quotient at every Euler-region
node. -/
theorem tendsto_eulerXiShiftFinitePrimeTheta
    {omega : ℝ} (homega : 0 < omega)
    {z : ℂ} (hz : z ∈ xiShiftEulerUpperSet omega) :
    Tendsto (fun S : Finset Nat.Primes => eulerXiShiftFinitePrimeTheta omega S z)
      atTop (nhds (eulerXiShiftTheta omega z)) := by
  have hp : Tendsto
      (fun S : Finset Nat.Primes => ∏ p ∈ S, eulerXiPrimeShiftFactor p omega z)
      atTop
      (nhds (riemannZeta (1 / 2 - (omega : ℂ) - z * I) /
        riemannZeta (1 / 2 + (omega : ℂ) - z * I))) :=
    eulerXiPrimeShiftFactor_hasProd homega hz
  have hmul := hp.const_mul (eulerXiArchimedeanQuotient omega z)
  rw [eulerXiShiftTheta_eq_archimedean_mul_zeta_ratio homega hz]
  simpa only [eulerXiShiftFinitePrimeTheta] using hmul

/-- Pick kernel formed from a finite prime approximation to the shifted completed-Xi quotient. -/
def eulerXiShiftFinitePrimePick
    (omega : ℝ) (S : Finset Nat.Primes) (z w : ℂ) : ℂ :=
  upperHalfPlaneSchurKernel (eulerXiShiftFinitePrimeTheta omega S) z w

/-- Finite-prime Pick entries converge to their exact all-prime values. -/
theorem tendsto_eulerXiShiftFinitePrimePick
    {omega : ℝ} (homega : 0 < omega)
    {z w : ℂ} (hz : z ∈ xiShiftEulerUpperSet omega)
    (hw : w ∈ xiShiftEulerUpperSet omega) :
    Tendsto (fun S : Finset Nat.Primes => eulerXiShiftFinitePrimePick omega S z w)
      atTop (nhds (eulerXiShiftPick omega z w)) := by
  have htz := tendsto_eulerXiShiftFinitePrimeTheta homega hz
  have htw := tendsto_eulerXiShiftFinitePrimeTheta homega hw
  have htwStar : Tendsto
      (fun S : Finset Nat.Primes =>
        (starRingEnd ℂ) (eulerXiShiftFinitePrimeTheta omega S w))
      atTop (nhds ((starRingEnd ℂ) (eulerXiShiftTheta omega w))) :=
    Complex.continuous_conj.continuousAt.tendsto.comp htw
  have hone : Tendsto (fun _ : Finset Nat.Primes => (1 : ℂ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hnumerator := hone.sub (htz.mul htwStar)
  have hkernel := hnumerator.const_mul (I / (z - (starRingEnd ℂ) w))
  simpa only [eulerXiShiftFinitePrimePick, upperHalfPlaneSchurKernel,
    eulerXiShiftPick_eq_upperHalfPlaneSchurKernel,
    ← eulerXiShiftTheta_eq_suzukiCanonicalTheta] using hkernel

/-- Every fixed finite rational-node coefficient energy of the finite prime kernel converges to its
exact all-prime energy. -/
theorem tendsto_eulerXiShiftFinitePrime_kernelForm
    {omega : ℝ} (homega : 0 < omega)
    (u : xiShiftEulerGaussianRationalSet omega →₀ ℂ) :
    Tendsto
      (fun S : Finset Nat.Primes =>
        kernelForm
          (fun z w : xiShiftEulerGaussianRationalSet omega =>
            eulerXiShiftFinitePrimePick omega S z.1 w.1) u u)
      atTop
      (nhds (kernelForm
        (fun z w : xiShiftEulerGaussianRationalSet omega =>
          eulerXiShiftPick omega z.1 w.1) u u)) := by
  classical
  have hinner (y : xiShiftEulerGaussianRationalSet omega) :
      Tendsto
        (fun S : Finset Nat.Primes => ∑ x ∈ u.support,
          (starRingEnd ℂ) (u y) * u x * eulerXiShiftFinitePrimePick omega S x.1 y.1)
        atTop
        (nhds (∑ x ∈ u.support,
          (starRingEnd ℂ) (u y) * u x * eulerXiShiftPick omega x.1 y.1)) := by
    apply tendsto_finset_sum_complex u.support
    intro x _
    exact (tendsto_eulerXiShiftFinitePrimePick homega x.2.1 y.2.1).const_mul
      ((starRingEnd ℂ) (u y) * u x)
  have houter := tendsto_finset_sum_complex u.support
    (fun y S => ∑ x ∈ u.support,
      (starRingEnd ℂ) (u y) * u x * eulerXiShiftFinitePrimePick omega S x.1 y.1)
    (fun y => ∑ x ∈ u.support,
      (starRingEnd ℂ) (u y) * u x * eulerXiShiftPick omega x.1 y.1)
    (fun y _ => hinner y)
  simpa only [kernelForm, Finsupp.sum] using houter

/-- A strictly negative exact Euler Pick energy has a finite prime approximation with twice a
positive rational margin and a certified tail smaller than that margin. -/
theorem exists_eulerXiShiftFinitePrime_negative_margin
    {omega : ℝ} (homega : 0 < omega)
    (u : xiShiftEulerGaussianRationalSet omega →₀ ℂ)
    (hneg : (kernelForm
      (fun z w : xiShiftEulerGaussianRationalSet omega =>
        eulerXiShiftPick omega z.1 w.1) u u).re < 0) :
    ∃ (S : Finset Nat.Primes) (delta : ℚ),
      0 < delta ∧
      (kernelForm
        (fun z w : xiShiftEulerGaussianRationalSet omega =>
          eulerXiShiftFinitePrimePick omega S z.1 w.1) u u).re ≤
        -2 * (delta : ℝ) ∧
      ‖kernelForm
          (fun z w : xiShiftEulerGaussianRationalSet omega =>
            eulerXiShiftFinitePrimePick omega S z.1 w.1) u u -
        kernelForm
          (fun z w : xiShiftEulerGaussianRationalSet omega =>
            eulerXiShiftPick omega z.1 w.1) u u‖ < (delta : ℝ) := by
  let q : ℝ := (kernelForm
    (fun z w : xiShiftEulerGaussianRationalSet omega =>
      eulerXiShiftPick omega z.1 w.1) u u).re
  have hq : q < 0 := hneg
  have hcomplex := tendsto_eulerXiShiftFinitePrime_kernelForm homega u
  have hreal : Tendsto
      (fun S : Finset Nat.Primes =>
        (kernelForm
          (fun z w : xiShiftEulerGaussianRationalSet omega =>
            eulerXiShiftFinitePrimePick omega S z.1 w.1) u u).re)
      atTop (nhds q) :=
    Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  have hquarterpos : 0 < -q / 4 := by linarith
  obtain ⟨delta, hdelta0, hdeltaupper⟩ := exists_rat_btwn hquarterpos
  have hdelta0Q : (0 : ℚ) < delta := by exact_mod_cast hdelta0
  have hdeltaReal : (0 : ℝ) < delta := hdelta0
  have heventuallyRe : ∀ᶠ S : Finset Nat.Primes in atTop,
      (kernelForm
        (fun z w : xiShiftEulerGaussianRationalSet omega =>
          eulerXiShiftFinitePrimePick omega S z.1 w.1) u u).re <
        q + (delta : ℝ) :=
    hreal (isOpen_Iio.mem_nhds (lt_add_of_pos_right q hdeltaReal))
  have heventuallyNorm : ∀ᶠ S : Finset Nat.Primes in atTop,
      ‖kernelForm
          (fun z w : xiShiftEulerGaussianRationalSet omega =>
            eulerXiShiftFinitePrimePick omega S z.1 w.1) u u -
        kernelForm
          (fun z w : xiShiftEulerGaussianRationalSet omega =>
            eulerXiShiftPick omega z.1 w.1) u u‖ < (delta : ℝ) := by
    have hball : Metric.ball
        (kernelForm
          (fun z w : xiShiftEulerGaussianRationalSet omega =>
            eulerXiShiftPick omega z.1 w.1) u u)
        (delta : ℝ) ∈ nhds
          (kernelForm
            (fun z w : xiShiftEulerGaussianRationalSet omega =>
              eulerXiShiftPick omega z.1 w.1) u u) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hdeltaReal)
    have hpre := hcomplex hball
    rw [Filter.mem_map] at hpre
    change ∀ᶠ S : Finset Nat.Primes in atTop,
      kernelForm
          (fun z w : xiShiftEulerGaussianRationalSet omega =>
            eulerXiShiftFinitePrimePick omega S z.1 w.1) u u ∈
        Metric.ball
          (kernelForm
            (fun z w : xiShiftEulerGaussianRationalSet omega =>
              eulerXiShiftPick omega z.1 w.1) u u)
          (delta : ℝ) at hpre
    simpa only [Metric.mem_ball, Complex.dist_eq] using hpre
  obtain ⟨S, hSre, hSnorm⟩ := (heventuallyRe.and heventuallyNorm).exists
  refine ⟨S, delta, hdelta0Q, ?_, hSnorm⟩
  have hcast : (delta : ℝ) < -q / 4 := hdeltaupper
  linarith

/-- The rational-margin finite-prime inequalities imply strict negativity of the exact all-prime
kernel energy. -/
theorem eulerXiShiftPick_negative_of_finitePrime_certificate
    {omega : ℝ}
    (u : xiShiftEulerGaussianRationalSet omega →₀ ℂ)
    (S : Finset Nat.Primes) (delta : ℚ)
    (hdelta : 0 < delta)
    (hfinite : (kernelForm
      (fun z w : xiShiftEulerGaussianRationalSet omega =>
        eulerXiShiftFinitePrimePick omega S z.1 w.1) u u).re ≤
      -2 * (delta : ℝ))
    (htail : ‖kernelForm
        (fun z w : xiShiftEulerGaussianRationalSet omega =>
          eulerXiShiftFinitePrimePick omega S z.1 w.1) u u -
      kernelForm
        (fun z w : xiShiftEulerGaussianRationalSet omega =>
          eulerXiShiftPick omega z.1 w.1) u u‖ < (delta : ℝ)) :
    (kernelForm
      (fun z w : xiShiftEulerGaussianRationalSet omega =>
        eulerXiShiftPick omega z.1 w.1) u u).re < 0 := by
  let A : ℂ := kernelForm
    (fun z w : xiShiftEulerGaussianRationalSet omega =>
      eulerXiShiftFinitePrimePick omega S z.1 w.1) u u
  let B : ℂ := kernelForm
    (fun z w : xiShiftEulerGaussianRationalSet omega =>
      eulerXiShiftPick omega z.1 w.1) u u
  have habs := Complex.abs_re_le_norm (A - B)
  have hlower : -‖A - B‖ ≤ (A - B).re := (abs_le.mp habs).1
  have hdeltaReal : (0 : ℝ) < delta := by exact_mod_cast hdelta
  change A.re ≤ -2 * (delta : ℝ) at hfinite
  change ‖A - B‖ < (delta : ℝ) at htail
  change B.re < 0
  simp only [Complex.sub_re] at hlower
  linarith

/-- Every uncancelled shifted pole yields a finite prime packet with a rational negative margin and
a certified all-prime tail on a finite Gaussian-rational node packet. -/
theorem exists_eulerXiShiftFinitePrime_certificate_of_uncancelled
    {omega : ℝ} (homega : 0 < omega) (q : XiShiftRightZeroCopy omega)
    (huncancel : suzukiCanonicalE omega (-xiShiftPoleCoordinate omega q) ≠ 0) :
    ∃ (u : xiShiftEulerGaussianRationalSet omega →₀ ℂ)
      (S : Finset Nat.Primes) (delta : ℚ),
      0 < delta ∧
      (kernelForm
        (fun z w : xiShiftEulerGaussianRationalSet omega =>
          eulerXiShiftFinitePrimePick omega S z.1 w.1) u u).re ≤
        -2 * (delta : ℝ) ∧
      ‖kernelForm
          (fun z w : xiShiftEulerGaussianRationalSet omega =>
            eulerXiShiftFinitePrimePick omega S z.1 w.1) u u -
        kernelForm
          (fun z w : xiShiftEulerGaussianRationalSet omega =>
            eulerXiShiftPick omega z.1 w.1) u u‖ < (delta : ℝ) := by
  obtain ⟨d, hd⟩ :=
    eulerXiShiftPick_gaussianRational_has_negativeDimension_one_of_uncancelled
      homega q huncancel
  let c : Fin 1 → ℂ := fun _ => 1
  have hc : c ≠ 0 := by
    intro hzero
    have h := congrFun hzero 0
    norm_num [c] at h
  let u : xiShiftEulerGaussianRationalSet omega →₀ ℂ := ∑ i, c i • d i
  have hneg : (kernelForm
      (fun z w : xiShiftEulerGaussianRationalSet omega =>
        eulerXiShiftPick omega z.1 w.1) u u).re < 0 := hd c hc
  obtain ⟨S, delta, hdelta, hfinite, htail⟩ :=
    exists_eulerXiShiftFinitePrime_negative_margin homega u hneg
  exact ⟨u, S, delta, hdelta, hfinite, htail⟩

/-- Under RH every exact shifted Euler Pick energy on Gaussian-rational nodes is nonnegative. -/
theorem eulerXiShiftPick_kernelForm_nonneg_of_riemannHypothesis
    (hRH : RiemannHypothesis) {omega : ℝ} (homega : 0 < omega)
    (u : xiShiftEulerGaussianRationalSet omega →₀ ℂ) :
    0 ≤ (kernelForm
      (fun z w : xiShiftEulerGaussianRationalSet omega =>
        eulerXiShiftPick omega z.1 w.1) u u).re := by
  letI : IsEmpty (XiShiftRightZeroCopy omega) := ⟨fun q => by
    letI := isEmpty_xiRightZeroCopy_of_riemannHypothesis hRH
    exact isEmptyElim (α := XiRightZeroCopy) ⟨q.1, homega.trans q.2⟩⟩
  have hnon : SuzukiShiftNonexceptional omega := fun q => isEmptyElim q
  have hmatrix :=
    (eulerXiShiftPick_noZero_iff_everySample_posSemidef homega hnon).mp inferInstance
  have hpsdEuler : IsPSDKernel
      (fun z w : xiShiftEulerUpperSet omega =>
        eulerXiShiftPick omega z.1 w.1) := by
    apply isPSDKernel_of_forall_posSemidef
    · intro z w
      exact star_eulerXiShiftPick_swap omega z.1 w.1
    · intro N w
      have h := (hmatrix N w).transpose
      have heq : (Matrix.of fun j k => eulerXiShiftPick omega (w j).1 (w k).1) =
          (eulerXiShiftPickSampleMatrix omega w).transpose := by
        ext i j
        rfl
      rw [heq]
      exact h
  have hpsd := hpsdEuler.comp
    (fun z : xiShiftEulerGaussianRationalSet omega =>
      (⟨z.1, z.2.1⟩ : xiShiftEulerUpperSet omega))
  exact hpsd.nonneg u

/-- Finite prime-side RH-failure certificate: a positive rational shift, finite
Gaussian-rational coefficient packet, finite prime packet, negative rational margin, and a
strictly smaller certified all-prime tail. -/
def XiShiftEulerFinitePrimeCertificate : Prop :=
  ∃ (omega : ℝ),
    0 < omega ∧
    (∃ r : ℚ, omega = (r : ℝ)) ∧
    ∃ (u : xiShiftEulerGaussianRationalSet omega →₀ ℂ)
      (S : Finset Nat.Primes) (delta : ℚ),
      0 < delta ∧
      (kernelForm
        (fun z w : xiShiftEulerGaussianRationalSet omega =>
          eulerXiShiftFinitePrimePick omega S z.1 w.1) u u).re ≤
        -2 * (delta : ℝ) ∧
      ‖kernelForm
          (fun z w : xiShiftEulerGaussianRationalSet omega =>
            eulerXiShiftFinitePrimePick omega S z.1 w.1) u u -
        kernelForm
          (fun z w : xiShiftEulerGaussianRationalSet omega =>
            eulerXiShiftPick omega z.1 w.1) u u‖ < (delta : ℝ)

/-- RH fails exactly when there is a finite, rigorously tail-certified prime-side Pick witness at a
positive rational shift and Gaussian-rational Euler nodes. -/
theorem not_riemannHypothesis_iff_xiShiftEulerFinitePrimeCertificate :
    ¬RiemannHypothesis ↔ XiShiftEulerFinitePrimeCertificate := by
  constructor
  · intro hRH
    obtain ⟨q₀⟩ := nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
    obtain ⟨omega, homega, _, hrat, q, _, huncancel⟩ :=
      exists_rational_shift_uncancelled_of_xiRightZeroCopy q₀
    obtain ⟨u, S, delta, hdelta, hfinite, htail⟩ :=
      exists_eulerXiShiftFinitePrime_certificate_of_uncancelled homega q huncancel
    exact ⟨omega, homega, hrat, u, S, delta, hdelta, hfinite, htail⟩
  · rintro ⟨omega, homega, _, u, S, delta, hdelta, hfinite, htail⟩ hRH
    have hneg := eulerXiShiftPick_negative_of_finitePrime_certificate
      u S delta hdelta hfinite htail
    exact (not_lt_of_ge
      (eulerXiShiftPick_kernelForm_nonneg_of_riemannHypothesis hRH homega u)) hneg

end

end RHTower
