import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# Completeness of four-edge phase relations

A four-edge multiset without a singleton vertex has only three product
types: paired edges, a triangle with a doubled edge, or a four-cycle.
Their explicit equations determine every such product, including repeated
edges and disconnected supports.
-/

noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ArithmeticEdges
set_option autoImplicit false

/-- Every endpoint occurs in another one of the four edge occurrences. -/
def NoSingleton4 {V : Type*} (a b c d e f g h : V) : Prop := ∀ w,
  ((w = a ∨ w = b) → w = c ∨ w = d ∨ w = e ∨ w = f ∨ w = g ∨ w = h) ∧
  ((w = c ∨ w = d) → w = a ∨ w = b ∨ w = e ∨ w = f ∨ w = g ∨ w = h) ∧
  ((w = e ∨ w = f) → w = a ∨ w = b ∨ w = c ∨ w = d ∨ w = g ∨ w = h) ∧
  ((w = g ∨ w = h) → w = a ∨ w = b ∨ w = c ∨ w = d ∨ w = e ∨ w = f)

namespace NoSingleton4
variable {V : Type*} {a b c d e f g h : V}

theorem flip_second (hn : NoSingleton4 a b c d e f g h) :
    NoSingleton4 a b d c e f g h := by
  simpa only [NoSingleton4,or_comm,or_left_comm,or_assoc,and_comm,and_left_comm,and_assoc] using hn

theorem flip_third (hn : NoSingleton4 a b c d e f g h) :
    NoSingleton4 a b c d f e g h := by
  simpa only [NoSingleton4,or_comm,or_left_comm,or_assoc,and_comm,and_left_comm,and_assoc] using hn

theorem flip_fourth (hn : NoSingleton4 a b c d e f g h) :
    NoSingleton4 a b c d e f h g := by
  simpa only [NoSingleton4,or_comm,or_left_comm,or_assoc,and_comm,and_left_comm,and_assoc] using hn

theorem swap_second_third (hn : NoSingleton4 a b c d e f g h) :
    NoSingleton4 a b e f c d g h := by
  simpa only [NoSingleton4,or_comm,or_left_comm,or_assoc,and_comm,and_left_comm,and_assoc] using hn

theorem swap_second_fourth (hn : NoSingleton4 a b c d e f g h) :
    NoSingleton4 a b g h e f c d := by
  simpa only [NoSingleton4,or_comm,or_left_comm,or_assoc,and_comm,and_left_comm,and_assoc] using hn

theorem swap_third_fourth (hn : NoSingleton4 a b c d e f g h) :
    NoSingleton4 a b c d g h e f := by
  simpa only [NoSingleton4,or_comm,or_left_comm,or_assoc,and_comm,and_left_comm,and_assoc] using hn

end NoSingleton4

/-- The explicit square, triangle and four-cycle equations. -/
structure QuarticRelations {V : Type*} (F G : V → V → ℝ) : Prop where
  square : ∀ a b, F a b ^ 2 = G a b ^ 2
  triangle : ∀ a b c, F a b * F a c * F b c ^ 2 = G a b * G a c * G b c ^ 2
  cycle : ∀ a b c d, F a b * F b c * F c d * F d a =
    G a b * G b c * G c d * G d a

def Agree4 {V : Type*} (F G : V → V → ℝ) (a b c d e f g h : V) : Prop :=
  F a b * F c d * F e f * F g h = G a b * G c d * G e f * G g h

variable {V : Type*} {F G : V → V → ℝ}

private theorem paired (H : QuarticRelations F G) (a b c d : V) :
    Agree4 F G a b a b c d c d := by
  unfold Agree4
  calc F a b * F a b * F c d * F c d = F a b ^ 2 * F c d ^ 2 := by ring
    _ = G a b ^ 2 * G c d ^ 2 := by rw [H.square,H.square]
    _ = G a b * G a b * G c d * G c d := by ring

variable (hF : ∀ a b, F a b = F b a) (hG : ∀ a b, G a b = G b a)
variable (H : QuarticRelations F G)
include hF hG H

private theorem double_joined (a b c d e : V) (hcd : c ≠ d) (hce : c ≠ e)
    (hn : NoSingleton4 a b a b c d c e) : Agree4 F G a b a b c d c e := by
  have hd : d = a ∨ d = b ∨ d = e := by
    have hdc := Ne.symm hcd
    have := (hn d).2.2.1 (Or.inr rfl)
    tauto
  have he : e = a ∨ e = b ∨ e = d := by
    have hec := Ne.symm hce
    have := (hn e).2.2.2 (Or.inr rfl)
    tauto
  by_cases hde : d = e
  · subst e
    exact paired H a b c d
  · have hd' : d = a ∨ d = b := by tauto
    have he' : e = a ∨ e = b := by have := Ne.symm hde; tauto
    rcases hd' with hd | hd <;> subst d <;> rcases he' with he | he <;> subst e
    all_goals first
      | exact (hde rfl).elim
      | simpa only [Agree4,pow_two,hF,hG,mul_comm,mul_left_comm,mul_assoc]
          using H.triangle c a b

private theorem double_edge (a b c d e f : V) (hcd : c ≠ d) (hef : e ≠ f)
    (hn : NoSingleton4 a b a b c d e f) : Agree4 F G a b a b c d e f := by
  by_cases hce : c = e
  · subst e
    exact double_joined hF hG H a b c d f hcd hef hn
  by_cases hcf : c = f
  · subst f
    have hn' : NoSingleton4 a b a b c d c e := hn.flip_fourth
    simpa only [Agree4,hF,hG,mul_comm,mul_left_comm,mul_assoc] using
      double_joined hF hG H a b c d e hcd hef.symm hn'
  by_cases hde : d = e
  · subst e
    have hn' : NoSingleton4 a b a b d c d f := hn.flip_third
    simpa only [Agree4,hF,hG,mul_comm,mul_left_comm,mul_assoc] using
      double_joined hF hG H a b d c f hcd.symm hef hn'
  by_cases hdf : d = f
  · subst f
    have hn' : NoSingleton4 a b a b d c d e := hn.flip_third.flip_fourth
    simpa only [Agree4,hF,hG,mul_comm,mul_left_comm,mul_assoc] using
      double_joined hF hG H a b d c e hcd.symm hef.symm hn'
  have hc : c = a ∨ c = b := by have := (hn c).2.2.1 (Or.inl rfl); tauto
  have hd : d = a ∨ d = b := by have := (hn d).2.2.1 (Or.inr rfl); tauto
  have he : e = a ∨ e = b := by
    have := (hn e).2.2.2 (Or.inl rfl)
    have := Ne.symm hce
    have := Ne.symm hde
    tauto
  have hf : f = a ∨ f = b := by
    have := (hn f).2.2.2 (Or.inr rfl)
    have := Ne.symm hcf
    have := Ne.symm hdf
    tauto
  rcases hc with hc | hc <;> subst c <;> rcases hd with hd | hd <;> subst d <;>
    rcases he with he | he <;> subst e <;> rcases hf with hf | hf <;> subst f
  all_goals first
    | exact (hcd rfl).elim
    | exact (hef rfl).elim
    | simpa only [Agree4,hF,hG,mul_comm,mul_left_comm,mul_assoc] using paired H a b a b

private theorem triangle_present (a b c d e : V) (hde : d ≠ e)
    (hn : NoSingleton4 a b a c b c d e) : Agree4 F G a b a c b c d e := by
  have hd : d = a ∨ d = b ∨ d = c := by
    have := (hn d).2.2.2 (Or.inl rfl)
    tauto
  have he : e = a ∨ e = b ∨ e = c := by
    have := (hn e).2.2.2 (Or.inr rfl)
    tauto
  rcases hd with hd | hd | hd <;> subst d <;> rcases he with he | he | he <;> subst e
  all_goals first
    | exact (hde rfl).elim
    | simpa only [Agree4,pow_two,hF,hG,mul_comm,mul_left_comm,mul_assoc]
        using H.triangle a b c
    | simpa only [Agree4,pow_two,hF,hG,mul_comm,mul_left_comm,mul_assoc]
        using H.triangle b a c
    | simpa only [Agree4,pow_two,hF,hG,mul_comm,mul_left_comm,mul_assoc]
        using H.triangle c a b

private theorem two_paths (a b c d e : V) (hbd : b ≠ d) (hce : c ≠ e)
    (hn : NoSingleton4 a b a c b d c e) : Agree4 F G a b a c b d c e := by
  have hd : d = a ∨ d = c ∨ d = e := by
    have := Ne.symm hbd
    have := (hn d).2.2.1 (Or.inr rfl)
    tauto
  have he : e = a ∨ e = b ∨ e = d := by
    have := Ne.symm hce
    have := (hn e).2.2.2 (Or.inr rfl)
    tauto
  by_cases hde : d = e
  · subst e
    simpa only [Agree4,hF,hG,mul_comm,mul_left_comm,mul_assoc] using H.cycle a b d c
  · have hd' : d = a ∨ d = c := by tauto
    have he' : e = a ∨ e = b := by have := Ne.symm hde; tauto
    rcases hd' with hd | hd <;> subst d <;> rcases he' with he | he <;> subst e
    all_goals first
      | exact (hde rfl).elim
      | simpa only [Agree4,pow_two,hF,hG,mul_comm,mul_left_comm,mul_assoc]
          using H.triangle a b c
      | simpa only [Agree4,pow_two,hF,hG,mul_comm,mul_left_comm,mul_assoc]
          using H.triangle b a c
      | simpa only [Agree4,pow_two,hF,hG,mul_comm,mul_left_comm,mul_assoc]
          using H.triangle c a b

private theorem wedge_extended (a b c d e f : V) (hac : a ≠ c) (hbc : b ≠ c)
    (hbd : b ≠ d) (hef : e ≠ f) (hn : NoSingleton4 a b a c b d e f) :
    Agree4 F G a b a c b d e f := by
  have hc : c = d ∨ c = e ∨ c = f := by
    have := Ne.symm hac
    have := Ne.symm hbc
    have := (hn c).2.1 (Or.inr rfl)
    tauto
  rcases hc with hc | hc | hc
  · subst d
    exact triangle_present hF hG H a b c e f hef hn
  · subst e
    exact two_paths hF hG H a b c d f hbd hef hn
  · subst f
    have hn' : NoSingleton4 a b a c b d c e := hn.flip_fourth
    simpa only [Agree4,hF,hG,mul_comm,mul_left_comm,mul_assoc] using
      two_paths hF hG H a b c d e hbd hef.symm hn'

private theorem wedge (a b c d e f g : V) (hab : a ≠ b) (hac : a ≠ c)
    (hde : d ≠ e) (hfg : f ≠ g) (hn : NoSingleton4 a b a c d e f g) :
    Agree4 F G a b a c d e f g := by
  by_cases hbc : b = c
  · subst c
    exact double_edge hF hG H a b d e f g hde hfg hn
  have hb : b = d ∨ b = e ∨ b = f ∨ b = g := by
    have := Ne.symm hab
    have := (hn b).1 (Or.inr rfl)
    tauto
  rcases hb with hb | hb | hb | hb
  · subst d
    exact wedge_extended hF hG H a b c e f g hac hbc hde hfg hn
  · subst e
    have hn' : NoSingleton4 a b a c b d f g := hn.flip_third
    simpa only [Agree4,hF,hG,mul_comm,mul_left_comm,mul_assoc] using
      wedge_extended hF hG H a b c d f g hac hbc hde.symm hfg hn'
  · subst f
    have hn' : NoSingleton4 a b a c b g d e := hn.swap_third_fourth
    simpa only [Agree4,hF,hG,mul_comm,mul_left_comm,mul_assoc] using
      wedge_extended hF hG H a b c g d e hac hbc hfg hde hn'
  · subst g
    have hn' : NoSingleton4 a b a c b f d e := hn.flip_fourth.swap_third_fourth
    simpa only [Agree4,hF,hG,mul_comm,mul_left_comm,mul_assoc] using
      wedge_extended hF hG H a b c f d e hac hbc hfg.symm hde hn'

/-- Squares, triangles and four-cycles exhaust four-edge products without singleton vertices. -/
theorem quartic_relations_complete (a b c d e f g h : V)
    (hab : a ≠ b) (hcd : c ≠ d) (hef : e ≠ f) (hgh : g ≠ h)
    (hn : NoSingleton4 a b c d e f g h) : Agree4 F G a b c d e f g h := by
  have ha : a = c ∨ a = d ∨ a = e ∨ a = f ∨ a = g ∨ a = h :=
    (hn a).1 (Or.inl rfl)
  rcases ha with ha | ha | ha | ha | ha | ha
  · subst c
    exact wedge hF hG H a b d e f g h hab hcd hef hgh hn
  · subst d
    have hn' : NoSingleton4 a b a c e f g h := hn.flip_second
    simpa only [Agree4,hF,hG,mul_comm,mul_left_comm,mul_assoc] using
      wedge hF hG H a b c e f g h hab hcd.symm hef hgh hn'
  · subst e
    have hn' : NoSingleton4 a b a f c d g h := hn.swap_second_third
    simpa only [Agree4,hF,hG,mul_comm,mul_left_comm,mul_assoc] using
      wedge hF hG H a b f c d g h hab hef hcd hgh hn'
  · subst f
    have hn' : NoSingleton4 a b a e c d g h := hn.flip_third.swap_second_third
    simpa only [Agree4,hF,hG,mul_comm,mul_left_comm,mul_assoc] using
      wedge hF hG H a b e c d g h hab hef.symm hcd hgh hn'
  · subst g
    have hn' : NoSingleton4 a b a h c d e f := hn.swap_second_fourth.swap_third_fourth
    simpa only [Agree4,hF,hG,mul_comm,mul_left_comm,mul_assoc] using
      wedge hF hG H a b h c d e f hab hgh hcd hef hn'
  · subst h
    have hn' : NoSingleton4 a b a g c d e f := hn.flip_fourth.swap_second_fourth.swap_third_fourth
    simpa only [Agree4,hF,hG,mul_comm,mul_left_comm,mul_assoc] using
      wedge hF hG H a b g c d e f hab hgh.symm hcd hef hn'

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ArithmeticEdges
