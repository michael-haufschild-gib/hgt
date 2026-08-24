import GaloisForLFunctions.RHTower.SemilocalDualPairEulerConnection
import GaloisForLFunctions.HTGeometry.DigammaGammaFactorialBlowUp
import GaloisForLFunctions.RHTower.RiemannXiRealAxisNonvanishing

/-!
# The unique finite-prime completed Euler pole

For a finite prime set, this file defines the card's literal completed logarithmic tangent in the
centered coordinate `s = 1/2 - i z`.  Existing corpus results supply the exact finite Euler
logarithmic source and its Lambert expansion.  The remaining rational, Gamma, and finite-prime
terms form a holomorphic regular part throughout the open upper half-plane.  Thus `z = i/2`, with
residue `-2i`, is the unique finite-prime upper pole.

The all-prime completed tangent is `-2 xi'/xi`; it is analytic at the same point because completed
Xi is nonzero at `s = 1`.  This is the exact local pole-cancellation statement.  No contractive
prime-to-divisor transfer is assumed or asserted.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The completed coordinate `s = 1/2 - i z`. -/
def eulerPoleCompletedCoordinate (z : ℂ) : ℂ := 1 / 2 - I * z

/-- Finite-place completed logarithmic tangent from the card. -/
def finitePrimeCompletedTangent (P : Finset Nat.Primes) (z : ℂ) : ℂ :=
  let s := eulerPoleCompletedCoordinate z
  ((-2 : ℂ) / s) - 2 / (s - 1) + (Real.log Real.pi : ℂ) -
      Complex.digamma (s / 2) +
    2 * (∑ p ∈ P, primeLogSource (p : ℕ) s)

/-- The tangent after deleting the Euler pole at `s = 1`. -/
def finitePrimeCompletedTangentRegularPart (P : Finset Nat.Primes) (z : ℂ) : ℂ :=
  let s := eulerPoleCompletedCoordinate z
  ((-2 : ℂ) / s) + (Real.log Real.pi : ℂ) - Complex.digamma (s / 2) +
    2 * (∑ p ∈ P, primeLogSource (p : ℕ) s)

theorem eulerPoleCompletedCoordinate_re (z : ℂ) :
    (eulerPoleCompletedCoordinate z).re = 1 / 2 + z.im := by
  simp [eulerPoleCompletedCoordinate]

theorem hasDerivAt_eulerPoleCompletedCoordinate (z : ℂ) :
    HasDerivAt eulerPoleCompletedCoordinate (-I) z := by
  have h : HasDerivAt (fun w : ℂ => (-I) * w + 1 / 2) (-I) z := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id z).const_mul (-I)).add_const (1 / 2 : ℂ)
  apply h.congr_of_eventuallyEq
  filter_upwards with w
  simp only [eulerPoleCompletedCoordinate]
  ring

private lemma differentiableAt_primeLogSource_of_re_pos
    (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (primeLogSource p) s := by
  exact (hasDerivAt_primeLogSource p.property.two_le
    (eulerLocalInverse_ne_zero p.property.two_le hs)).differentiableAt

private theorem analyticAt_logDeriv_xi_of_ne {z : ℂ} (hz : xi z ≠ 0) :
    AnalyticAt ℂ (logDeriv xi) z := by
  have hxi : AnalyticAt ℂ xi z :=
    xi_differentiable.differentiableOn.analyticAt (Filter.univ_mem' fun _ => trivial)
  exact hxi.deriv.div hxi hz

/-- After the Euler pole is removed, every finite-prime completed tangent is holomorphic on the
whole open upper half-plane. -/
theorem differentiableAt_finitePrimeCompletedTangentRegularPart
    (P : Finset Nat.Primes) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (finitePrimeCompletedTangentRegularPart P) z := by
  have hs : 0 < (eulerPoleCompletedCoordinate z).re := by
    rw [eulerPoleCompletedCoordinate_re]
    linarith
  have hs0 : eulerPoleCompletedCoordinate z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hcoord := hasDerivAt_eulerPoleCompletedCoordinate z
  have hrat : DifferentiableAt ℂ
      (fun w : ℂ => -2 / eulerPoleCompletedCoordinate w) z :=
    (differentiableAt_const (c := (-2 : ℂ))).div hcoord.differentiableAt hs0
  have hhalf : HasDerivAt (fun w : ℂ => eulerPoleCompletedCoordinate w / 2) (-I / 2) z :=
    hcoord.div_const 2
  have hhalfRe : 0 < (eulerPoleCompletedCoordinate z / 2).re := by
    rw [Complex.div_re]
    norm_num
    linarith
  have hdigAt : AnalyticAt ℂ Complex.digamma (eulerPoleCompletedCoordinate z / 2) :=
    GaloisForLFunctions.analyticAt_digamma_of_offPoles (by
      intro p hp
      have hre := congrArg Complex.re hp
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      have hpnonneg : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      linarith)
  have hdig : DifferentiableAt ℂ
      (fun w : ℂ => Complex.digamma (eulerPoleCompletedCoordinate w / 2)) z :=
    hdigAt.differentiableAt.comp z hhalf.differentiableAt
  have hprime : DifferentiableAt ℂ
      (fun w : ℂ => ∑ p ∈ P,
        primeLogSource (p : ℕ) (eulerPoleCompletedCoordinate w)) z := by
    classical
    induction P using Finset.induction_on with
    | empty => simp
    | @insert p P hp ih =>
        simp only [Finset.sum_insert hp]
        exact ((differentiableAt_primeLogSource_of_re_pos p hs).comp z
          hcoord.differentiableAt).add ih
  unfold finitePrimeCompletedTangentRegularPart
  dsimp only
  exact
    (((hrat.add (differentiableAt_const (c := (Real.log Real.pi : ℂ)))).sub hdig).add
      ((differentiableAt_const (c := (2 : ℂ))).mul hprime))

theorem finitePrimeCompletedTangent_eq_regularPart_sub_pole
    (P : Finset Nat.Primes) (z : ℂ) :
    finitePrimeCompletedTangent P z =
      finitePrimeCompletedTangentRegularPart P z -
        2 / (eulerPoleCompletedCoordinate z - 1) := by
  simp only [finitePrimeCompletedTangent, finitePrimeCompletedTangentRegularPart]
  ring

theorem eulerPoleCompletedCoordinate_sub_one (z : ℂ) :
    eulerPoleCompletedCoordinate z - 1 = -I * (z - I / 2) := by
  rw [eulerPoleCompletedCoordinate]
  ring_nf
  rw [I_sq]
  ring

/-- The finite-prime upper pole has the exact residue `-2i`. -/
theorem tendsto_finitePrimeCompletedTangent_eulerPoleResidue
    (P : Finset Nat.Primes) :
    Tendsto (fun z : ℂ => (z - I / 2) * finitePrimeCompletedTangent P z)
      (nhdsWithin (I / 2) ({I / 2}ᶜ)) (nhds (-2 * I)) := by
  have hz0 : 0 < (I / 2 : ℂ).im := by norm_num
  have hreg :=
    (differentiableAt_finitePrimeCompletedTangentRegularPart P hz0).continuousAt
  have hzero : Tendsto (fun z : ℂ => z - I / 2) (nhds (I / 2)) (nhds 0) := by
    have h : Tendsto (fun z : ℂ => z) (nhds (I / 2)) (nhds (I / 2)) :=
      continuousAt_id
    simpa only [sub_self] using h.sub_const (I / 2)
  have hregzero : Tendsto
      (fun z : ℂ => (z - I / 2) * finitePrimeCompletedTangentRegularPart P z)
      (nhdsWithin (I / 2) ({I / 2}ᶜ)) (nhds 0) := by
    change Tendsto
      (fun z : ℂ => (z - I / 2) * finitePrimeCompletedTangentRegularPart P z)
      (nhds (I / 2) ⊓ Filter.principal ({I / 2}ᶜ)) (nhds 0)
    simpa only [zero_mul] using (hzero.mono_left inf_le_left).mul
      (hreg.mono_left inf_le_left)
  have hpole :
      (fun z : ℂ => (z - I / 2) *
        (-2 / (eulerPoleCompletedCoordinate z - 1))) =ᶠ[nhdsWithin (I / 2) ({I / 2}ᶜ)]
        fun _ => -2 * I := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ I / 2 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
    have hne : z - I / 2 ≠ 0 := sub_ne_zero.mpr hz'
    rw [eulerPoleCompletedCoordinate_sub_one]
    let x := z - I / 2
    have hx : x ≠ 0 := hne
    change x * (-2 / (-I * x)) = -2 * I
    field_simp [hx, I_ne_zero]
    ring_nf
    rw [I_sq]
    ring
  have hsum := hregzero.add hpole.tendsto
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards with z
  rw [finitePrimeCompletedTangent_eq_regularPart_sub_pole]
  ring

theorem differentiableAt_finitePrimeCompletedTangent_of_ne_eulerPole
    (P : Finset Nat.Primes) {z : ℂ} (hz : 0 < z.im) (hne : z ≠ I / 2) :
    DifferentiableAt ℂ (finitePrimeCompletedTangent P) z := by
  have hden : eulerPoleCompletedCoordinate z - 1 ≠ 0 := by
    rw [eulerPoleCompletedCoordinate_sub_one]
    exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (sub_ne_zero.mpr hne)
  have hpole : DifferentiableAt ℂ
      (fun w : ℂ => 2 / (eulerPoleCompletedCoordinate w - 1)) z :=
    (differentiableAt_const (c := (2 : ℂ))).div
      ((hasDerivAt_eulerPoleCompletedCoordinate z).differentiableAt.sub
        (differentiableAt_const (c := (1 : ℂ)))) hden
  rw [show finitePrimeCompletedTangent P = fun w =>
      finitePrimeCompletedTangentRegularPart P w -
        2 / (eulerPoleCompletedCoordinate w - 1) by
    funext w
    exact finitePrimeCompletedTangent_eq_regularPart_sub_pole P w]
  exact (differentiableAt_finitePrimeCompletedTangentRegularPart P hz).sub hpole

theorem not_differentiableAt_finitePrimeCompletedTangent_eulerPole
    (P : Finset Nat.Primes) :
    ¬ DifferentiableAt ℂ (finitePrimeCompletedTangent P) (I / 2) := by
  intro hdiff
  have hzero : Tendsto (fun z : ℂ => z - I / 2) (nhds (I / 2)) (nhds 0) := by
    have h : Tendsto (fun z : ℂ => z) (nhds (I / 2)) (nhds (I / 2)) :=
      continuousAt_id
    simpa only [sub_self] using h.sub_const (I / 2)
  have hprod :
      Tendsto (fun z : ℂ => (z - I / 2) * finitePrimeCompletedTangent P z)
        (nhdsWithin (I / 2) ({I / 2}ᶜ)) (nhds 0) := by
    change Tendsto (fun z : ℂ => (z - I / 2) * finitePrimeCompletedTangent P z)
      (nhds (I / 2) ⊓ Filter.principal ({I / 2}ᶜ)) (nhds 0)
    simpa only [zero_mul] using (hzero.mono_left inf_le_left).mul
      (hdiff.continuousAt.mono_left inf_le_left)
  have hres := tendsto_finitePrimeCompletedTangent_eulerPoleResidue P
  have heq : (0 : ℂ) = -2 * I := tendsto_nhds_unique hprod hres
  have hne : (-2 * I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) I_ne_zero
  exact hne heq.symm

/-- The uncancelled Euler pole is the unique failure of holomorphy in the open upper half-plane. -/
theorem differentiableAt_finitePrimeCompletedTangent_iff
    (P : Finset Nat.Primes) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (finitePrimeCompletedTangent P) z ↔ z ≠ I / 2 := by
  constructor
  · intro h hzero
    subst z
    exact not_differentiableAt_finitePrimeCompletedTangent_eulerPole P h
  · exact differentiableAt_finitePrimeCompletedTangent_of_ne_eulerPole P hz

/-- The all-prime completed tangent, whose Euler pole has cancelled. -/
def allPrimeCompletedTangent (z : ℂ) : ℂ :=
  -2 * logDeriv xi (eulerPoleCompletedCoordinate z)

/-- Completion cancels the finite-prime Euler pole: the all-prime tangent is analytic at `z=i/2`. -/
theorem analyticAt_allPrimeCompletedTangent_eulerPole :
    AnalyticAt ℂ allPrimeCompletedTangent (I / 2) := by
  have hcoord : AnalyticAt ℂ eulerPoleCompletedCoordinate (I / 2) :=
    analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  have hcoordVal : eulerPoleCompletedCoordinate (I / 2) = 1 := by
    rw [eulerPoleCompletedCoordinate]
    ring_nf
    rw [I_sq]
    ring
  have hxi : xi (1 : ℂ) ≠ 0 := xi_ne_zero_of_ofReal 1
  have hlog : AnalyticAt ℂ (logDeriv xi) (1 : ℂ) := analyticAt_logDeriv_xi_of_ne hxi
  change AnalyticAt ℂ
    (fun z => -2 * logDeriv xi (eulerPoleCompletedCoordinate z)) (I / 2)
  have hcomp : AnalyticAt ℂ
      (fun z => logDeriv xi (eulerPoleCompletedCoordinate z)) (I / 2) := by
    change AnalyticAt ℂ ((logDeriv xi) ∘ eulerPoleCompletedCoordinate) (I / 2)
    exact hlog.comp_of_eq hcoord hcoordVal
  exact analyticAt_const.mul hcomp

end

end RHTower
