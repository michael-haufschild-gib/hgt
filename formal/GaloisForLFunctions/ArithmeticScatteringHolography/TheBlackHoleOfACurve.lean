import GaloisForLFunctions.ArithmeticScatteringHolography.TheHasseWindow
import GaloisForLFunctions.RHTower.EllipticCurveHasseBound

/-!
# The black hole of an elliptic curve

An elliptic curve `W` over a finite field gives channel data: `G = W(𝔽_q)`, and the points of the `x`-line give
the local count, since a point of the `x`-line has at most two rational points above it, namely `±P`
(`ellipticChannels`). The trace of the black hole is the trace of Frobenius.

Over the true curve, Hasse's theorem places the trace in the window, so **every resonance is at the universal
rate** (`elliptic_universal_damping`). This calibrates the programme: universal damping holds here, and the
proof in the corpus goes through Stepanov's auxiliary section and the Gauss-sum modulus, not through the wave
equation.
-/

open Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.ArithmeticScatteringHolography

section Group

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- A map to a finite set whose fibres lie in `{P, -P}` bounds the channel count. -/
theorem card_add_card_le_of_fibres {S : Type*} [Fintype S] [DecidableEq S] (x : G → S)
    (hx : ∀ P R, x P = x R → R = P ∨ R = -P) :
    Fintype.card (TwoTorsion G) + Fintype.card G ≤ 2 * Fintype.card S := by
  set w : G → ℝ := fun P => if 2 • P = 0 then 1 else 1 / 2 with hw
  have hw0 (P : G) : 0 ≤ w P := by
    simp only [hw]
    split_ifs <;> norm_num
  have hsum : ∑ P, w P = ((Fintype.card (TwoTorsion G) : ℝ) + Fintype.card G) / 2 := by
    have hcard : ((univ.filter fun P : G => 2 • P = 0).card : ℝ) = Fintype.card (TwoTorsion G) := by
      rw [Fintype.card_subtype]
    have hcompl : (((univ.filter fun P : G => ¬ 2 • P = 0).card : ℕ) : ℝ) =
        (Fintype.card G : ℝ) - Fintype.card (TwoTorsion G) := by
      rw [← hcard, eq_sub_iff_add_eq, ← Nat.cast_add, add_comm,
        Finset.card_filter_add_card_filter_not, Finset.card_univ]
    simp only [hw]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hcard, hcompl]
    ring
  have hfibre (s : S) : ∑ P ∈ univ.filter (fun P => x P = s), w P ≤ 1 := by
    rcases (univ.filter fun P => x P = s).eq_empty_or_nonempty with he | ⟨P₀, hP₀⟩
    · rw [he]
      simp
    · have hP₀' : x P₀ = s := (Finset.mem_filter.mp hP₀).2
      have hsub : (univ.filter fun P => x P = s) ⊆ {P₀, -P₀} := by
        intro R hR
        have hR' : x R = s := (Finset.mem_filter.mp hR).2
        rcases hx P₀ R (hP₀'.trans hR'.symm) with h | h
        · simp [h]
        · simp [h]
      refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun P _ _ => hw0 P).trans ?_
      by_cases htors : 2 • P₀ = 0
      · have hneg : -P₀ = P₀ := by
          have : P₀ + P₀ = 0 := by rw [← two_nsmul]; exact htors
          exact neg_eq_of_add_eq_zero_left this
        rw [hneg, Finset.pair_eq_singleton, Finset.sum_singleton]
        simp [hw, htors]
      · have hne : P₀ ≠ -P₀ := by
          intro h
          apply htors
          rw [two_nsmul]
          nth_rewrite 1 [h]
          simp
        rw [Finset.sum_pair hne]
        have htors' : ¬ 2 • (-P₀) = 0 := by rwa [two_nsmul_neg_eq_zero_iff]
        simp only [hw, if_neg htors, if_neg htors']
        norm_num
  have hle : ∑ P, w P ≤ Fintype.card S := by
    rw [← Finset.sum_fiberwise (s := univ) (g := x) (f := w)]
    calc ∑ s, ∑ P ∈ univ.filter (fun P => x P = s), w P
        ≤ ∑ _s : S, (1 : ℝ) := Finset.sum_le_sum fun s _ => hfibre s
      _ = Fintype.card S := by simp
  rw [hsum] at hle
  have : ((Fintype.card (TwoTorsion G) : ℝ) + Fintype.card G) ≤ 2 * Fintype.card S := by linarith
  exact_mod_cast this

/-- `h - a` is even: the points off two-torsion come in pairs `±P`. -/
theorem even_card_add_card : Even (Fintype.card (TwoTorsion G) + Fintype.card G) := by
  set s := univ.filter fun P : G => ¬ 2 • P = 0 with hs
  have hcount : Fintype.card G = Fintype.card (TwoTorsion G) + s.card := by
    rw [Fintype.card_subtype, hs, Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hzero : ((s.card : ℕ) : ZMod 2) = 0 := by
    have h := Finset.sum_involution (s := s) (f := fun _ => (1 : ZMod 2)) (fun P _ => -P)
      (fun _ _ => by decide)
      (fun P hP _ h0 => by
        have hP' := (Finset.mem_filter.mp hP).2
        apply hP'
        rw [two_nsmul]
        nth_rewrite 1 [← h0]
        simp)
      (fun P hP => by
        have hP' := (Finset.mem_filter.mp hP).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [two_nsmul_neg_eq_zero_iff]⟩)
      (fun P _ => neg_neg P)
    simpa using h
  have heven : Even s.card := (ZMod.natCast_eq_zero_iff_even).mp hzero
  rw [hcount]
  obtain ⟨m, hm⟩ := heven
  exact ⟨Fintype.card (TwoTorsion G) + m, by omega⟩

/-- **Channel data from a group.** Any finite abelian group whose two-torsion and order fit under `2(q+1)`
gives a black hole, with `(2(q+1) - a - h)/2` dead ends. -/
def Channels.ofGroup (q : ℕ) (hq : 2 ≤ q)
    (hle : Fintype.card (TwoTorsion G) + Fintype.card G ≤ 2 * (q + 1)) :
    Channels G (Fin ((2 * (q + 1) - (Fintype.card (TwoTorsion G) + Fintype.card G)) / 2)) where
  q := q
  two_le := hq
  count := by
    rw [Fintype.card_fin]
    obtain ⟨m, hm⟩ := even_card_add_card (G := G)
    omega

end Group

section Curve

attribute [local instance] Classical.propDecidable

open WeierstrassCurve

variable {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F) [W.IsElliptic]

instance : Finite W.toAffine.Point :=
  haveI : Finite (WithZero {xy : F × F // W.toAffine.Equation xy.1 xy.2}) :=
    inferInstanceAs (Finite (Option {xy : F × F // W.toAffine.Equation xy.1 xy.2}))
  Finite.of_equiv _ (Affine.pointEquiv W.toAffine).symm

instance : Fintype W.toAffine.Point := Fintype.ofFinite _

/-- The `x`-coordinate of a point, with `∞` for the neutral element. -/
def xLine : W.toAffine.Point → Option F
  | .zero => none
  | .some x _ _ => some x

theorem xLine_fibres (P R : W.toAffine.Point) (h : xLine W P = xLine W R) : R = P ∨ R = -P := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases R with _ | ⟨x₂, y₂, h₂⟩
  · exact Or.inl rfl
  · simp [xLine] at h
  · simp [xLine] at h
  · have hx : x₁ = x₂ := by simpa [xLine] using h
    rcases Affine.Point.X_eq_iff.mp hx with h' | h'
    · exact Or.inl h'.symm
    · right
      rw [h', neg_neg]

/-- The local count of an elliptic curve: `a + h ≤ 2(q + 1)`. -/
theorem elliptic_count :
    Fintype.card (TwoTorsion W.toAffine.Point) + Fintype.card W.toAffine.Point ≤
      2 * (Fintype.card F + 1) := by
  have := card_add_card_le_of_fibres (xLine W) (xLine_fibres W)
  simpa [Fintype.card_option] using this

/-- **The black hole of an elliptic curve.** -/
def ellipticChannels : Channels W.toAffine.Point
    (Fin ((2 * (Fintype.card F + 1) -
      (Fintype.card (TwoTorsion W.toAffine.Point) + Fintype.card W.toAffine.Point)) / 2)) :=
  Channels.ofGroup (Fintype.card F)
    (by
      have := Fintype.one_lt_card (α := F)
      omega)
    (elliptic_count W)

/-- The trace of the black hole of a curve is the trace of Frobenius. -/
theorem traceR_ellipticChannels :
    (ellipticChannels W).traceR = (Fintype.card F : ℝ) + 1 - Nat.card W.toAffine.Point := by
  unfold Channels.traceR
  rw [Nat.card_eq_fintype_card]
  rfl

/-- **The black hole of a curve lies in the Hasse window.** -/
theorem elliptic_trace_sq_le (hF : ringChar F ≠ 2) :
    (ellipticChannels W).traceR ^ 2 ≤ 4 * (ellipticChannels W).q := by
  have h := RHTower.EllipticHasse.abs_natCard_point_sub_le W hF
  rw [traceR_ellipticChannels]
  have hq : (ellipticChannels W).q = Fintype.card F := rfl
  rw [hq]
  have hsq : Real.sqrt (Fintype.card F) ^ 2 = Fintype.card F :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have h1 := (abs_le.mp h).1
  have h2 := (abs_le.mp h).2
  have hr : 0 ≤ Real.sqrt (Fintype.card F) := Real.sqrt_nonneg _
  nlinarith

/-- **Universal damping on the black hole of a curve.** Every root of the Frobenius polynomial has
`|a|² = q`, and rings at rate `¼`. -/
theorem elliptic_universal_damping (hF : ringChar F ≠ 2) {a : ℂ}
    (ha : a ^ 2 - ((ellipticChannels W).traceR : ℂ) * a + ((ellipticChannels W).q : ℂ) = 0) :
    dampingRate (ellipticChannels W).q a = 1 / 4 := by
  have hq2 := (ellipticChannels W).q_pos
  have hq0 : (0 : ℝ) < (ellipticChannels W).q := by linarith
  have hq1 : (1 : ℝ) < (ellipticChannels W).q := by linarith
  have h := (modes_on_circle_iff hq0).mpr (elliptic_trace_sq_le W hF) a (by exact_mod_cast ha)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Complex.normSq_zero] at h
    linarith
  rw [dampingRate_eq_quarter_iff hq1 ha0, ← Complex.normSq_eq_norm_sq]
  exact h

end Curve

end GaloisForLFunctions.ArithmeticScatteringHolography

end
