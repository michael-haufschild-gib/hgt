import GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowCancellation
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.RHLadderTheory

/-!
# Sharp prime-window cancellation collides with the first multiplicity rung

The pole-cancelled dyadic sharp source loses exactly one vanishing order at every shifted
right-half Xi zero.  Every such shifted point lies in `1 < Re s < 3/2`.  If the cancelled source
has even divisor on that band, while the first nontrivial multiplicity rung makes every right-half
Xi order even, the exact one-order loss makes the two constraints incompatible.  An analytic
square of the cancelled source is a constructive sufficient condition; source zero-freeness is
retained only as a stronger corollary.
-/

open Complex Filter Function Set

noncomputable section

namespace RHTower

/-- Source-only zero-freeness of the explicit pole-cancelled dyadic sharp prime expression on the
half-plane containing every shifted right-half Xi pole. -/
def DyadicSharpPrimeCancelledSourceRightZeroFree : Prop :=
  ∀ s : ℂ, 1 < s.re → dyadicSharpPrimeCancelledSource s ≠ 0

/-- The shifted pole-filled zeta has exactly the same vanishing order as Xi at the underlying
right-half divisor point.  The translation has nonzero derivative, while both the regularizing
linear factor and the archimedean Xi factor are local units in the open critical strip. -/
theorem analyticOrderAt_shiftedRegularizedZeta_eq_xi_order
    (q : XiRightZeroCopy) :
    analyticOrderAt
        (fun s : ℂ => regularizedRiemannZeta (s - 1 / 2))
        (xiRightShiftedPole q) =
      analyticOrderAt xi (q.1.1 : ℂ) := by
  let p : ℂ := xiRightShiftedPole q
  let ρ : ℂ := (q.1.1 : ℂ)
  have hpρ : p - 1 / 2 = ρ := by
    simpa only [p, ρ] using xiRightShiftedPole_sub_half q
  have hcenterRe := congrArg Complex.re
    (xiRightCenteredZero_eq_support_sub_half q)
  simp only [Complex.sub_re] at hcenterRe
  norm_num at hcenterRe
  have hcenterBounds := abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)
  have hρpos : 0 < ρ.re := by
    dsimp only [ρ]
    linarith
  have hρlt : ρ.re < 1 := by
    dsimp only [ρ]
    linarith
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hρlt
    exact (lt_irrefl 1 hρlt).elim
  have hregEqZeta :
      analyticOrderAt regularizedRiemannZeta ρ =
        analyticOrderAt riemannZeta ρ := by
    have hev : regularizedRiemannZeta =ᶠ[nhds ρ]
        fun z => (z - 1) * riemannZeta z := by
      filter_upwards [isOpen_ne.mem_nhds hρ1] with z hz
      exact regularizedRiemannZeta_of_ne_one hz
    have hlin : AnalyticAt ℂ (fun z : ℂ => z - 1) ρ := by fun_prop
    have hzeta : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ1
    rw [analyticOrderAt_congr hev]
    change analyticOrderAt ((fun z : ℂ => z - 1) * riemannZeta) ρ =
      analyticOrderAt riemannZeta ρ
    rw [analyticOrderAt_mul hlin hzeta,
      hlin.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hρ1), zero_add]
  let shift : ℂ → ℂ := fun z => z - 1 / 2
  have hshiftAn : AnalyticAt ℂ shift p := by
    dsimp only [shift]
    fun_prop
  have hshiftDeriv : deriv shift p ≠ 0 := by
    dsimp only [shift]
    rw [deriv_sub_const, deriv_id'']
    norm_num
  have hshiftOrder := analyticOrderAt_comp_of_deriv_ne_zero
    (f := regularizedRiemannZeta) hshiftAn hshiftDeriv
  have hleft : analyticOrderAt
      (fun s : ℂ => regularizedRiemannZeta (s - 1 / 2)) p =
      analyticOrderAt regularizedRiemannZeta ρ := by
    rw [show shift p = ρ by simpa only [shift] using hpρ] at hshiftOrder
    change analyticOrderAt
      (fun s : ℂ => regularizedRiemannZeta (s - 1 / 2)) p =
        analyticOrderAt regularizedRiemannZeta ρ at hshiftOrder
    exact hshiftOrder
  calc
    analyticOrderAt
        (fun s : ℂ => regularizedRiemannZeta (s - 1 / 2))
        (xiRightShiftedPole q) =
      analyticOrderAt regularizedRiemannZeta ρ := by
        simpa only [p] using hleft
    _ = analyticOrderAt riemannZeta ρ := hregEqZeta
    _ = analyticOrderAt xi ρ :=
      (xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hρpos, hρlt⟩).symm
    _ = analyticOrderAt xi (q.1.1 : ℂ) := by rfl

/-- The narrow continuation band containing every shifted right-half Xi pole. -/
def dyadicSharpPrimeCollisionBand : Set ℂ :=
  {s : ℂ | 1 < s.re ∧ s.re < 3 / 2}

/-- Every shifted right-half Xi pole lies strictly inside the collision band.  In particular, it
lies to the left of the ordinary Dirichlet-series half-plane `Re s > 3/2`. -/
theorem xiRightShiftedPole_mem_dyadicSharpPrimeCollisionBand
    (q : XiRightZeroCopy) :
    xiRightShiftedPole q ∈ dyadicSharpPrimeCollisionBand := by
  rw [dyadicSharpPrimeCollisionBand, Set.mem_setOf_eq, xiRightShiftedPole,
    Complex.add_re, Complex.one_re]
  have hbounds := abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)
  constructor
  · linarith [xiRightCenteredZero_re_pos q]
  · linarith

/-- The relevant shifted Xi poles never lie in the ordinary absolute-convergence half-plane used
by the Dirichlet-series identity. -/
theorem not_three_halves_lt_re_xiRightShiftedPole (q : XiRightZeroCopy) :
    ¬3 / 2 < (xiRightShiftedPole q).re := by
  have hband := xiRightShiftedPole_mem_dyadicSharpPrimeCollisionBand q
  exact not_lt_of_ge (le_of_lt hband.2)

/-- Intrinsic source parity on the only band relevant to the cancellation collision: every local
vanishing order of the explicit cancelled sharp source is even.  Nonzero points contribute order
zero, so this permits source zeros of arbitrary even positive multiplicity. -/
def DyadicSharpPrimeCancelledSourceEvenOrderOnCollisionBand : Prop :=
  ∀ s ∈ dyadicSharpPrimeCollisionBand,
    Even (analyticOrderAt dyadicSharpPrimeCancelledSource s).toNat

/-- A source-side square factorization of the cancelled sharp source on the collision band.  This
is a constructive sufficient condition for even local source order. -/
def DyadicSharpPrimeCancelledSourceSquareOnCollisionBand : Prop :=
  ∃ g : ℂ → ℂ,
    AnalyticOnNhd ℂ g dyadicSharpPrimeCollisionBand ∧
      ∀ s ∈ dyadicSharpPrimeCollisionBand,
        g s ^ (2 : ℕ) = dyadicSharpPrimeCancelledSource s

/-- An analytic square factorization forces every cancelled-source order in the collision band to
be even, including the locally identically-zero case whose extended-natural order has `toNat = 0`.
-/
theorem dyadicSharpPrimeCancelledSourceEvenOrderOnCollisionBand_of_square
    (h : DyadicSharpPrimeCancelledSourceSquareOnCollisionBand) :
    DyadicSharpPrimeCancelledSourceEvenOrderOnCollisionBand := by
  obtain ⟨g, hg, hsq⟩ := h
  intro s hs
  have hopen : IsOpen dyadicSharpPrimeCollisionBand := by
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hev : dyadicSharpPrimeCancelledSource =ᶠ[nhds s] g ^ (2 : ℕ) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact (hsq z hz).symm
  have horder : analyticOrderAt dyadicSharpPrimeCancelledSource s =
      2 • analyticOrderAt g s := by
    rw [analyticOrderAt_congr hev]
    exact analyticOrderAt_pow (hg s hs) 2
  rw [horder]
  generalize ho : analyticOrderAt g s = o
  induction o using ENat.recTopCoe with
  | top => simp
  | coe n =>
      change Even (2 * n)
      exact ⟨n, by omega⟩

/-- Half-plane zero-freeness is stronger than the intrinsic even-order condition on the collision
band. -/
theorem dyadicSharpPrimeCancelledSourceEvenOrderOnCollisionBand_of_rightZeroFree
    (hzeroFree : DyadicSharpPrimeCancelledSourceRightZeroFree) :
    DyadicSharpPrimeCancelledSourceEvenOrderOnCollisionBand := by
  intro s hs
  have hne : dyadicSharpPrimeCancelledSource s ≠ 0 := hzeroFree s hs.1
  rw [analyticOrderAt_eq_zero.mpr (Or.inr hne)]
  exact Even.zero

/-- **Adjacent-parity collision.**  If both Xi and the explicit cancelled source carry even local
orders on their respective source-defined regions, the exact order drop by one excludes every
right-half Xi zero and proves RH. -/
theorem riemannHypothesis_of_rhLadder_one_of_dyadicSharpPrimeCancelledSource_evenOrder
    (hsourceParity : DyadicSharpPrimeCancelledSourceEvenOrderOnCollisionBand)
    (hxiParity : RHLadder 1) :
    RiemannHypothesis := by
  by_contra hRH
  let q : XiRightZeroCopy :=
    Classical.choice (nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH)
  let p : ℂ := xiRightShiftedPole q
  let ρ : ℂ := (q.1.1 : ℂ)
  have hpBand : p ∈ dyadicSharpPrimeCollisionBand := by
    exact xiRightShiftedPole_mem_dyadicSharpPrimeCollisionBand q
  obtain ⟨m, hregOrder, hsourceOrder⟩ :=
    analyticOrderAt_dyadicSharpPrimeCancelledSource_eq_pred q
  have hsourceEven := hsourceParity p hpBand
  have hsourceNat :
      (analyticOrderAt dyadicSharpPrimeCancelledSource p).toNat = m := by
    rw [hsourceOrder]
    rfl
  rw [hsourceNat] at hsourceEven
  have hxiOrder : analyticOrderAt xi ρ = (m + 1 : ℕ) := by
    have hbridge := analyticOrderAt_shiftedRegularizedZeta_eq_xi_order q
    dsimp only [p, ρ] at hregOrder ⊢
    rw [hbridge] at hregOrder
    exact hregOrder
  have hρright : ρ ∈ rightHalf := by
    rw [mem_rightHalf]
    have hcenterRe := congrArg Complex.re
      (xiRightCenteredZero_eq_support_sub_half q)
    simp only [Complex.sub_re] at hcenterRe
    norm_num at hcenterRe
    dsimp only [ρ]
    linarith [xiRightCenteredZero_re_pos q]
  have hρzero : xi ρ = 0 := by
    dsimp only [ρ]
    exact xi_eq_zero_of_mem_divisor_support q.1.1
  have hxiEven := (rhLadder_one_iff_even_order.mp hxiParity) ρ hρright hρzero
  have hxiNat : (analyticOrderAt xi ρ).toNat = m + 1 := by
    rw [hxiOrder]
    rfl
  rw [hxiNat] at hxiEven
  obtain ⟨a, ha⟩ := hsourceEven
  obtain ⟨b, hb⟩ := hxiEven
  omega

/-- Any positive ladder rung contains the first Xi parity rung, so the adjacent-parity collision
works with `RHLadder k` for every `k ≥ 1`. -/
theorem riemannHypothesis_of_rhLadder_of_dyadicSharpPrimeCancelledSource_evenOrder
    {k : ℕ} (hk : 1 ≤ k)
    (hsourceParity : DyadicSharpPrimeCancelledSourceEvenOrderOnCollisionBand)
    (hladder : RHLadder k) :
    RiemannHypothesis :=
  riemannHypothesis_of_rhLadder_one_of_dyadicSharpPrimeCancelledSource_evenOrder
    hsourceParity (rhLadder_imp_one hk hladder)

/-- A source-side analytic square of the explicit cancelled sharp source, together with only the
first Xi multiplicity rung, proves RH. -/
theorem riemannHypothesis_of_rhLadder_one_of_dyadicSharpPrimeCancelledSource_square
    (hsourceSquare : DyadicSharpPrimeCancelledSourceSquareOnCollisionBand)
    (hxiParity : RHLadder 1) :
    RiemannHypothesis :=
  riemannHypothesis_of_rhLadder_one_of_dyadicSharpPrimeCancelledSource_evenOrder
    (dyadicSharpPrimeCancelledSourceEvenOrderOnCollisionBand_of_square hsourceSquare)
    hxiParity

/-- **Sharp-cancellation/parity collision.**  Zero-freeness of the explicit cancelled source on
`Re s > 1`, together with only the first dyadic multiplicity rung, forces RH. -/
theorem riemannHypothesis_of_rhLadder_one_of_dyadicSharpPrimeCancelledSource_rightZeroFree
    (hzeroFree : DyadicSharpPrimeCancelledSourceRightZeroFree)
    (hparity : RHLadder 1) :
    RiemannHypothesis := by
  by_contra hRH
  let q : XiRightZeroCopy :=
    Classical.choice (nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH)
  let p : ℂ := xiRightShiftedPole q
  let ρ : ℂ := (q.1.1 : ℂ)
  have hp : 1 < p.re := by
    dsimp only [p]
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
    linarith [xiRightCenteredZero_re_pos q]
  have hsourceNe : dyadicSharpPrimeCancelledSource p ≠ 0 := hzeroFree p hp
  obtain ⟨m, hregOrder, hsourceOrder⟩ :=
    analyticOrderAt_dyadicSharpPrimeCancelledSource_eq_pred q
  have hsourceZero : analyticOrderAt dyadicSharpPrimeCancelledSource p = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hsourceNe)
  have hm0 : m = 0 := by
    rw [hsourceZero] at hsourceOrder
    exact_mod_cast hsourceOrder.symm
  subst m
  have hxiOrder : analyticOrderAt xi ρ = (1 : ℕ) := by
    have hbridge := analyticOrderAt_shiftedRegularizedZeta_eq_xi_order q
    dsimp only [p, ρ] at hregOrder ⊢
    rw [hbridge] at hregOrder
    simpa using hregOrder
  have hρright : ρ ∈ rightHalf := by
    rw [mem_rightHalf]
    have hcenterRe := congrArg Complex.re
      (xiRightCenteredZero_eq_support_sub_half q)
    simp only [Complex.sub_re] at hcenterRe
    norm_num at hcenterRe
    dsimp only [ρ]
    linarith [xiRightCenteredZero_re_pos q]
  have hρzero : xi ρ = 0 := by
    dsimp only [ρ]
    exact xi_eq_zero_of_mem_divisor_support q.1.1
  have heven := (rhLadder_one_iff_even_order.mp hparity) ρ hρright hρzero
  have htoNat : (analyticOrderAt xi ρ).toNat = 1 := by
    rw [hxiOrder]
    rfl
  rw [htoNat] at heven
  obtain ⟨k, hk⟩ := heven
  omega

/-- Any positive ladder rung contains the first parity rung, so the same source zero-freeness
collides with `RHLadder k` for every `k ≥ 1`. -/
theorem riemannHypothesis_of_rhLadder_of_dyadicSharpPrimeCancelledSource_rightZeroFree
    {k : ℕ} (hk : 1 ≤ k)
    (hzeroFree : DyadicSharpPrimeCancelledSourceRightZeroFree)
    (hladder : RHLadder k) :
    RiemannHypothesis :=
  riemannHypothesis_of_rhLadder_one_of_dyadicSharpPrimeCancelledSource_rightZeroFree
    hzeroFree (rhLadder_imp_one hk hladder)

end RHTower
