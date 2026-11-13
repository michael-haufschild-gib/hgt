import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheAntisymmetricStateOfTheTwoEndsIsBoundedBelowIffTheRiemannHypothesis
import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.ShortWindowsCarryAtMostOneNegativeSquare
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteWeilSourceTransfer

/-!
# A uniform lower bound on the margin forces the Riemann hypothesis

The margin of a window is the second eigenvalue of its form: the least `m` such that every plane
of packets in the window contains a nonzero packet with `N ≥ m · mass` (`MarginBoundedBelow`).
Under RH the margin of every window is nonnegative: every plane meets the hyperplane of vanishing
first charge, on which the neutral form is Weil's form of the zeros. The converse holds with
any constant:

  **RH iff the margins of all windows are bounded below** (`riemannHypothesis_iff_margin_bddBelow`).

Proof of the converse. Without RH the lag structure `S` of the pole-free profile is unbounded
above and below: an upper or a lower bound forces RH by Landau's argument from either side
(`riemannHypothesis_of_lagStructure_le`, `riemannHypothesis_of_le_lagStructure`). The symmetric
and the antisymmetric state of the two ends have neutral forms `2 Re S(0) ± 2 Re S(v)`
(`neutralForm_twoEndEven`, `neutralForm_twoEndOdd`), so for suitable lengths both become as
deep as we like. They are even and odd about the same centre, hence orthogonal both for the
neutral form — the reflection fixes the form (`neutralForm_reflect`) and changes the sign of the
odd part (`neutralForm_even_add_odd`) — and for the mass (`integral_even_mul_odd`). On their
plane the neutral form is `a² N(e) + b² N(o)`, below any given multiple of the mass.

So the second bound state that RH excludes cannot be confined to a bounded depth: either there
is none, or windows carry two bound states of unbounded depth, one symmetric and one
antisymmetric in their two ends.
-/

open MeasureTheory Complex
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx)
open GaloisForLFunctions.SquareRootThreshold (lagStructure)
open Zeta23

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

/-- **The margins of all windows are bounded below by `−C`**: every plane of smooth packets on a
window `[−L, L]`, with contacts up to `Q > e^{2L}`, contains a nonzero packet `a x + b y` with
`N(a x + b y) ≥ −C ∫ (a x + b y)²`. -/
def MarginBoundedBelow (C : ℝ) : Prop :=
  ∀ (x y : ℝ → ℝ) (L : ℝ), ContDiff ℝ 2 x → ContDiff ℝ 2 y →
    (∀ u, L < |u| → x u = 0 ∧ y u = 0) → ∀ Q : ℕ, Real.exp (2 * L) < Q →
      ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
        -(C * ∫ u, (a * x u + b * y u) ^ 2) ≤ neutralForm Q (fun u => a * x u + b * y u)

/-! ### Packets on a window -/

theorem lt_abs_of_not_mem_Icc {L u : ℝ} (hu : u ∉ Set.Icc (-L) L) : L < |u| := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
  rcases hu with h | h
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs u)
  · exact lt_of_lt_of_le h (le_abs_self u)

theorem hasCompactSupport_of_vanishing {g : ℝ → ℝ} {L : ℝ} (hg : ∀ u, L < |u| → g u = 0) :
    HasCompactSupport g :=
  HasCompactSupport.intro (isCompact_Icc (a := -L) (b := L)) fun u hu =>
    hg u (lt_abs_of_not_mem_Icc hu)

/-- A packet on `[−L, L]` has no contacts beyond `e^{2L}`. -/
theorem packetAutocorr_log_eq_zero_of_vanishing {g : ℝ → ℝ} {L : ℝ}
    (hg : ∀ u, L < |u| → g u = 0) {Q : ℕ} (hQ : Real.exp (2 * L) < Q) :
    ∀ n : ℕ, Q < n → packetAutocorr g (Real.log n) = 0 := by
  intro n hn
  have hn' : Real.exp (2 * L) < n := hQ.trans (by exact_mod_cast hn)
  have hlog : 2 * L < Real.log n :=
    (Real.lt_log_iff_exp_lt (by exact_mod_cast (show 0 < n by omega))).mpr hn'
  refine packetAutocorr_eq_zero_of_vanishing_off (a := -L) (b := L) (fun u hu => hg u ?_)
    (by linarith)
  rcases hu with h | h
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs u)
  · exact lt_of_lt_of_le h (le_abs_self u)

theorem integrable_mul_exp_neg_half_of_vanishing {g : ℝ → ℝ} (hg : Continuous g) {L : ℝ}
    (hv : ∀ u, L < |u| → g u = 0) : Integrable fun u => g u * Real.exp (-u / 2) :=
  (hg.mul (by fun_prop)).integrable_of_hasCompactSupport (hasCompactSupport_of_vanishing hv).mul_right

/-- On a pole-free packet the neutral form is Weil's form. -/
theorem neutralForm_eq_weilQuad {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    {Q : ℕ} (hQ : ∀ n : ℕ, Q < n → packetAutocorr g (Real.log n) = 0)
    (hA : ∫ u, g u * Real.exp (-u / 2) = 0) :
    neutralForm Q g = SpacingScaleHarmonicAnalysis.weilQuad g := by
  rw [neutralForm_eq_re_sub hg hgc hQ, Complex.sub_re, poleConfig_W_ofReal, Complex.ofReal_re, hA,
    zero_mul, mul_zero, sub_zero, ArithmeticCastelnuovoSeveri.LogCells.weilQuad_eq_zetaW hg hgc]

/-- The neutral form is homogeneous of degree two. -/
theorem neutralForm_smul (Q : ℕ) (c : ℝ) (g : ℝ → ℝ) :
    neutralForm Q (fun u => c * g u) = c ^ 2 * neutralForm Q g := by
  have hA : ∀ x, packetAutocorr (fun u => c * g u) x = c ^ 2 * packetAutocorr g x := fun x => by
    unfold packetAutocorr
    rw [← integral_const_mul]
    congr 1
    funext u
    ring
  have hJ : ∀ x, levyJump (fun u => c * g u) x = c ^ 2 * levyJump g x := fun x => by
    unfold levyJump
    rw [hA, hA]
    ring
  have e : ∑ k ∈ Finset.Icc 2 Q, contactWeight k * (c ^ 2 * packetAutocorr g (Real.log k)) =
      c ^ 2 * ∑ k ∈ Finset.Icc 2 Q, contactWeight k * packetAutocorr g (Real.log k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [neutralForm_eq, neutralForm_eq]
  simp only [hA, hJ]
  rw [integral_const_mul, e]
  ring

/-! ### The even and the odd part are orthogonal -/

/-- **On the plane of an even and an odd pole-free packet the neutral form is diagonal**:
`N(e + t o) = N(e) + t² N(o)`. The reflection fixes the neutral form and sends `e + t o` to
`e − t o`, so the cross term of Weil's form vanishes. -/
theorem neutralForm_even_add_odd {e o : ℝ → ℝ} (he : ContDiff ℝ 2 e) (ho : ContDiff ℝ 2 o)
    {L : ℝ} (hv : ∀ u, L < |u| → e u = 0 ∧ o u = 0) (heven : ∀ u, e (-u) = e u)
    (hodd : ∀ u, o (-u) = -o u) (hAe : ∫ u, e u * Real.exp (-u / 2) = 0)
    (hAo : ∫ u, o u * Real.exp (-u / 2) = 0) {Q : ℕ} (hQ : Real.exp (2 * L) < Q) (t : ℝ) :
    neutralForm Q (fun u => e u + t * o u) = neutralForm Q e + t ^ 2 * neutralForm Q o := by
  have hve : ∀ u, L < |u| → e u = 0 := fun u hu => (hv u hu).1
  have hvo : ∀ u, L < |u| → o u = 0 := fun u hu => (hv u hu).2
  have hvs : ∀ s : ℝ, ∀ u, L < |u| → e u + s * o u = 0 := fun s u hu => by
    rw [(hv u hu).1, (hv u hu).2, mul_zero, add_zero]
  have hsmooth : ∀ s : ℝ, ContDiff ℝ 2 fun u => e u + s * o u := fun s =>
    he.add (contDiff_const.mul ho)
  have hcharge : ∀ s : ℝ, ∫ u, (e u + s * o u) * Real.exp (-u / 2) = 0 := fun s => by
    have hie := integrable_mul_exp_neg_half_of_vanishing he.continuous hve
    have hio := integrable_mul_exp_neg_half_of_vanishing ho.continuous hvo
    have e1 : (fun u => (e u + s * o u) * Real.exp (-u / 2)) =
        fun u => e u * Real.exp (-u / 2) + s * (o u * Real.exp (-u / 2)) := by
      funext u; ring
    rw [e1, integral_add hie (hio.const_mul s), integral_const_mul, hAe, hAo, mul_zero,
      add_zero]
  have hW : ∀ s : ℝ, neutralForm Q (fun u => e u + s * o u) =
      SpacingScaleHarmonicAnalysis.weilQuad (fun u => e u + s * o u) := fun s =>
    neutralForm_eq_weilQuad (hsmooth s) (hasCompactSupport_of_vanishing (hvs s))
      (packetAutocorr_log_eq_zero_of_vanishing (hvs s) hQ) (hcharge s)
  have hreal : ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, L < |u| → f u = 0) →
      f ∈ ArithmeticCastelnuovoSeveri.realTests := fun f hf hfv =>
    ⟨hf, hasCompactSupport_of_vanishing hfv⟩
  have hexp := CohomologyOfWindowsOfSpecZ.weilQuad_add_smul (hreal e he hve) (hreal o ho hvo)
  -- the reflection fixes the neutral form
  have hrefl : neutralForm Q (fun u => e u + 1 * o u) = neutralForm Q (fun u => e u + -1 * o u) := by
    have h := neutralForm_reflect Q 0 (fun u => e u + 1 * o u)
    have hr : reflectPacket 0 (fun u => e u + 1 * o u) = fun u => e u + -1 * o u := by
      funext u
      simp only [reflectPacket, zero_sub, heven, hodd]
      ring
    rw [hr] at h
    exact h.symm
  rw [hW, hW, hexp 1, hexp (-1)] at hrefl
  have hP : ArithmeticCastelnuovoSeveri.weilPair e o = 0 := by linarith
  have h0 : neutralForm Q e = SpacingScaleHarmonicAnalysis.weilQuad e :=
    neutralForm_eq_weilQuad he (hasCompactSupport_of_vanishing hve)
      (packetAutocorr_log_eq_zero_of_vanishing hve hQ) hAe
  have h1 : neutralForm Q o = SpacingScaleHarmonicAnalysis.weilQuad o :=
    neutralForm_eq_weilQuad ho (hasCompactSupport_of_vanishing hvo)
      (packetAutocorr_log_eq_zero_of_vanishing hvo hQ) hAo
  rw [hW, hexp t, hP, h0, h1]
  ring

/-- An even and an odd packet are orthogonal for the mass. -/
theorem integral_even_mul_odd {e o : ℝ → ℝ} (heven : ∀ u, e (-u) = e u)
    (hodd : ∀ u, o (-u) = -o u) : ∫ u, e u * o u = 0 := by
  have h := integral_neg_eq_self (fun u => e u * o u) volume
  simp only [heven, hodd, mul_neg, integral_neg] at h
  linarith

theorem integral_even_add_odd_sq {e o : ℝ → ℝ} (he : Continuous e) (ho : Continuous o) {L : ℝ}
    (hv : ∀ u, L < |u| → e u = 0 ∧ o u = 0) (heven : ∀ u, e (-u) = e u)
    (hodd : ∀ u, o (-u) = -o u) (a b : ℝ) :
    ∫ u, (a * e u + b * o u) ^ 2 = a ^ 2 * (∫ u, e u ^ 2) + b ^ 2 * ∫ u, o u ^ 2 := by
  have hint : ∀ f : ℝ → ℝ, Continuous f → (∀ u, L < |u| → f u = 0) → Integrable f :=
    fun f hf hfv => hf.integrable_of_hasCompactSupport (hasCompactSupport_of_vanishing hfv)
  have hv2 : ∀ u, L < |u| → e u ^ 2 = 0 := fun u hu => by rw [(hv u hu).1]; ring
  have hv3 : ∀ u, L < |u| → o u ^ 2 = 0 := fun u hu => by rw [(hv u hu).2]; ring
  have hv4 : ∀ u, L < |u| → e u * o u = 0 := fun u hu => by rw [(hv u hu).1]; ring
  have i1 : Integrable fun u => a ^ 2 * e u ^ 2 :=
    (hint (fun u => e u ^ 2) (he.pow 2) hv2).const_mul _
  have i2 : Integrable fun u => b ^ 2 * o u ^ 2 :=
    (hint (fun u => o u ^ 2) (ho.pow 2) hv3).const_mul _
  have i3 : Integrable fun u => 2 * a * b * (e u * o u) :=
    (hint (fun u => e u * o u) (he.mul ho) hv4).const_mul _
  have e1 : (fun u => (a * e u + b * o u) ^ 2) =
      fun u => a ^ 2 * e u ^ 2 + (2 * a * b * (e u * o u) + b ^ 2 * o u ^ 2) := by
    funext u; ring
  have h1 : ∫ u, (a ^ 2 * e u ^ 2 + (2 * a * b * (e u * o u) + b ^ 2 * o u ^ 2)) =
      (∫ u, a ^ 2 * e u ^ 2) + ∫ u, (2 * a * b * (e u * o u) + b ^ 2 * o u ^ 2) :=
    integral_add i1 (i3.add i2)
  have h2 : ∫ u, (2 * a * b * (e u * o u) + b ^ 2 * o u ^ 2) =
      (∫ u, 2 * a * b * (e u * o u)) + ∫ u, b ^ 2 * o u ^ 2 :=
    integral_add i3 i2
  rw [e1, h1, h2, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_even_mul_odd heven hodd]
  ring

/-! ### The theorem -/

theorem twoEnd_vanishing (V v : ℝ) :
    ∀ u, 5 + (|V| + |v|) / 2 < |u| → twoEndEven V u = 0 ∧ twoEndOdd v u = 0 := fun u hu =>
  ⟨twoEndEven_eq_zero V (by have := abs_nonneg v; linarith),
    twoEndOdd_eq_zero v (by have := abs_nonneg V; linarith)⟩

/-- **RH iff the margins of all windows are bounded below.** -/
theorem riemannHypothesis_iff_margin_bddBelow :
    RiemannHypothesis ↔ ∃ C : ℝ, MarginBoundedBelow C := by
  constructor
  · -- every plane meets the hyperplane of vanishing first charge
    intro hRH
    refine ⟨0, fun x y L hx hy hv Q hQ => ?_⟩
    have hvx : ∀ u, L < |u| → x u = 0 := fun u hu => (hv u hu).1
    have hvy : ∀ u, L < |u| → y u = 0 := fun u hu => (hv u hu).2
    obtain ⟨Ax, hAx⟩ : ∃ A, A = ∫ u, x u * Real.exp (-u / 2) := ⟨_, rfl⟩
    obtain ⟨Ay, hAy⟩ : ∃ A, A = ∫ u, y u * Real.exp (-u / 2) := ⟨_, rfl⟩
    have hix := integrable_mul_exp_neg_half_of_vanishing hx.continuous hvx
    have hiy := integrable_mul_exp_neg_half_of_vanishing hy.continuous hvy
    have hcharge : ∀ a b : ℝ, ∫ u, (a * x u + b * y u) * Real.exp (-u / 2) = a * Ax + b * Ay := by
      intro a b
      have e1 : (fun u => (a * x u + b * y u) * Real.exp (-u / 2)) =
          fun u => a * (x u * Real.exp (-u / 2)) + b * (y u * Real.exp (-u / 2)) := by
        funext u; ring
      rw [e1, integral_add (hix.const_mul a) (hiy.const_mul b), integral_const_mul,
        integral_const_mul, hAx, hAy]
    obtain ⟨a, b, hab, hA⟩ : ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ a * Ax + b * Ay = 0 := by
      by_cases h0 : Ax = 0
      · exact ⟨1, 0, Or.inl one_ne_zero, by rw [h0]; ring⟩
      · exact ⟨Ay, -Ax, Or.inr (neg_ne_zero.mpr h0), by ring⟩
    refine ⟨a, b, hab, ?_⟩
    have hvs : ∀ u, L < |u| → a * x u + b * y u = 0 := fun u hu => by
      rw [hvx u hu, hvy u hu]; ring
    rw [zero_mul, neg_zero]
    exact neutralForm_nonneg_of_charge_eq_zero hRH ((contDiff_const.mul hx).add
      (contDiff_const.mul hy)) (hasCompactSupport_of_vanishing hvs)
      (packetAutocorr_log_eq_zero_of_vanishing hvs hQ) (by
        show ∫ u, (a * x u + b * y u) * Real.exp (-u / 2) = 0
        rw [hcharge, hA])
  · -- without RH two deep orthogonal states, one even and one odd
    rintro ⟨C, hC⟩
    by_contra hRH
    obtain ⟨S0, hS0⟩ : ∃ S, S = 2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) 0).re :=
      ⟨_, rfl⟩
    obtain ⟨m₀, hm₀def⟩ : ∃ m, m = ∫ u, poleFreeProfile u ^ 2 := ⟨_, rfl⟩
    have hm₀ : 0 ≤ m₀ := by rw [hm₀def]; exact integral_nonneg fun u => sq_nonneg _
    obtain ⟨D, hD⟩ : ∃ D, D = |S0| + 4 * |C| * m₀ + 1 := ⟨_, rfl⟩
    -- the lag structure is unbounded above and below
    obtain ⟨v, hv0, hvS⟩ : ∃ v : ℝ, 0 ≤ v ∧
        S0 + D < 2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) v).re := by
      by_contra h
      push Not at h
      exact hRH (riemannHypothesis_of_lagStructure_le h)
    obtain ⟨V, hV0, hVS⟩ : ∃ V : ℝ, 0 ≤ V ∧
        2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) V).re < -(S0 + D) := by
      by_contra h
      push Not at h
      exact hRH (riemannHypothesis_of_le_lagStructure (M := S0 + D) h)
    obtain ⟨L, hL⟩ : ∃ L, L = 5 + (|V| + |v|) / 2 := ⟨_, rfl⟩
    have hv : ∀ u, L < |u| → twoEndEven V u = 0 ∧ twoEndOdd v u = 0 := fun u hu =>
      twoEnd_vanishing V v u (by rw [← hL]; exact hu)
    obtain ⟨Q, hQ⟩ := exists_nat_gt (Real.exp (2 * L))
    obtain ⟨a, b, hab, hineq⟩ := hC (twoEndEven V) (twoEndOdd v) L (contDiff_twoEndEven V)
      (contDiff_twoEndOdd v) hv Q hQ
    have hvE : ∀ u, L < |u| → twoEndEven V u = 0 := fun u hu => (hv u hu).1
    have hvO : ∀ u, L < |u| → twoEndOdd v u = 0 := fun u hu => (hv u hu).2
    have hNE := neutralForm_twoEndEven V (packetAutocorr_log_eq_zero_of_vanishing hvE hQ)
    have hNO := neutralForm_twoEndOdd v (packetAutocorr_log_eq_zero_of_vanishing hvO hQ)
    have hmE := integral_twoEndEven_sq_le V
    have hmO := integral_twoEndOdd_sq_le v
    rw [← hm₀def] at hmE hmO
    rw [← hS0] at hNE hNO
    have hmE0 : 0 ≤ ∫ u, twoEndEven V u ^ 2 := integral_nonneg fun u => sq_nonneg _
    have hmO0 : 0 ≤ ∫ u, twoEndOdd v u ^ 2 := integral_nonneg fun u => sq_nonneg _
    -- the plane is diagonal for the form and for the mass
    have hmass := integral_even_add_odd_sq (contDiff_twoEndEven V).continuous
      (contDiff_twoEndOdd v).continuous hv (twoEndEven_neg V) (twoEndOdd_neg v) a b
    have hform : neutralForm Q (fun u => a * twoEndEven V u + b * twoEndOdd v u) =
        a ^ 2 * neutralForm Q (twoEndEven V) + b ^ 2 * neutralForm Q (twoEndOdd v) := by
      by_cases ha : a = 0
      · subst ha
        have e1 : (fun u => 0 * twoEndEven V u + b * twoEndOdd v u) =
            fun u => b * twoEndOdd v u := by funext u; ring
        rw [e1, neutralForm_smul]
        ring
      · have e1 : (fun u => a * twoEndEven V u + b * twoEndOdd v u) =
            fun u => a * (twoEndEven V u + b / a * twoEndOdd v u) := by
          funext u; field_simp
        have hab2 : a ^ 2 * (b / a) ^ 2 = b ^ 2 := by rw [← mul_pow, mul_div_cancel₀ b ha]
        rw [e1, neutralForm_smul, neutralForm_even_add_odd (contDiff_twoEndEven V)
          (contDiff_twoEndOdd v) hv (twoEndEven_neg V) (twoEndOdd_neg v) (charge_twoEndEven V)
          (charge_twoEndOdd v) hQ (b / a), mul_add, ← mul_assoc, hab2]
    rw [hform, hmass, hNE, hNO] at hineq
    -- both states lie below `−|C|` times their mass, by at least one
    have hE : S0 + 2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) V).re ≤
        -(|C| * ∫ u, twoEndEven V u ^ 2) - 1 := by
      have := mul_le_mul_of_nonneg_left hmE (abs_nonneg C)
      linarith [le_abs_self S0, abs_nonneg S0]
    have hO : S0 - 2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) v).re ≤
        -(|C| * ∫ u, twoEndOdd v u ^ 2) - 1 := by
      have := mul_le_mul_of_nonneg_left hmO (abs_nonneg C)
      linarith [le_abs_self S0, abs_nonneg S0]
    have hpos : 0 < a ^ 2 + b ^ 2 := by
      rcases hab with h | h
      · have := pow_pos (abs_pos.mpr h) 2
        rw [sq_abs] at this
        nlinarith [sq_nonneg b]
      · have := pow_pos (abs_pos.mpr h) 2
        rw [sq_abs] at this
        nlinarith [sq_nonneg a]
    have hCa : -(C * (a ^ 2 * (∫ u, twoEndEven V u ^ 2) + b ^ 2 * ∫ u, twoEndOdd v u ^ 2)) ≥
        -(|C| * (a ^ 2 * (∫ u, twoEndEven V u ^ 2) + b ^ 2 * ∫ u, twoEndOdd v u ^ 2)) := by
      have hnn : 0 ≤ a ^ 2 * (∫ u, twoEndEven V u ^ 2) + b ^ 2 * ∫ u, twoEndOdd v u ^ 2 :=
        add_nonneg (mul_nonneg (sq_nonneg a) hmE0) (mul_nonneg (sq_nonneg b) hmO0)
      nlinarith [le_abs_self C]
    linarith [mul_le_mul_of_nonneg_left hE (sq_nonneg a),
      mul_le_mul_of_nonneg_left hO (sq_nonneg b)]

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
