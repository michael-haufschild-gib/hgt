import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # A positive finite clock cancelling prescribed spectral frequencies -/
open Finset Real
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
noncomputable section

/-- At each step, stay put or advance by a positive half-period, with equal weight. -/
def average : List ℝ → (ℝ → ℂ) → ℝ → ℂ
  | [], f, a => f a
  | w :: ws, f, a => (average ws f a+average ws f (a+π/|w|))/2

/-- Total diameter of the sample record. -/
def length (ws : List ℝ) := (ws.map (fun w => π/|w|)).sum

/-- A phase wave on continuous physical time. -/
def wave (w t : ℝ) : ℂ := Complex.exp (((w*t:ℝ):ℂ)*Complex.I)

theorem wave_add (w a h : ℝ) : wave w (a+h)=wave w a*wave w h := by
  simp only [wave,mul_add,Complex.ofReal_add,add_mul,Complex.exp_add]

private theorem wave_half {w v : ℝ} (hw : w≠0) (he : |w|=|v|) : wave w (π/|v|)= -1 := by
  rw [←he]
  rcases lt_or_gt_of_ne hw with hn|hp
  · rw [abs_of_neg hn,wave,show w*(π/(-w))= -π by field_simp,Complex.ofReal_neg,neg_mul,
      Complex.exp_neg,Complex.exp_pi_mul_I]
    norm_num
  · rw [abs_of_pos hp,wave,show w*(π/w)=π by field_simp,Complex.exp_pi_mul_I]

theorem average_const (ws : List ℝ) (c : ℂ) (a : ℝ) : average ws (fun _ => c) a=c := by
  induction ws generalizing a with
  | nil => rfl
  | cons v vs ih => rw [average,ih,ih]; ring

theorem average_scale (ws : List ℝ) (c : ℂ) (f : ℝ → ℂ) (a : ℝ) :
    average ws (fun t => c*f t) a=c*average ws f a := by
  induction ws generalizing a with
  | nil => rfl
  | cons v vs ih => rw [average,average,ih,ih]; ring

theorem average_sum {I : Type*} (S : Finset I) (ws : List ℝ) (f : I → ℝ → ℂ) (a : ℝ) :
    average ws (fun t => ∑ i ∈ S, f i t) a=∑ i ∈ S, average ws (f i) a := by
  induction ws generalizing a with
  | nil => rfl
  | cons v vs ih => simp only [average,ih,←sum_add_distrib,sum_div]

/-- Factorization holds at every frequency, including unlisted ones. -/
theorem average_wave (ws : List ℝ) (w a : ℝ) :
    average ws (wave w) a=wave w a*(ws.map (fun v => (1+wave w (π/|v|))/2)).prod := by
  induction ws generalizing a with
  | nil => simp [average]
  | cons v vs ih => simp only [average,ih,wave_add,List.map_cons,List.prod_cons]; ring

/-- One half-period of either sign of w kills the entire Fourier coefficient. -/
theorem annihilate (ws : List ℝ) {w : ℝ} (hw : w≠0) (h : ∃ v∈ws, |w|=|v|) (a : ℝ) :
    average ws (wave w) a=0 := by
  obtain ⟨v,hv,he⟩ := h
  rw [average_wave]
  have hz : (0:ℂ) ∈ ws.map (fun v => (1+wave w (π/|v|))/2) := by
    exact List.mem_map.mpr ⟨v,hv,by rw [wave_half hw he]; ring⟩
  rw [List.prod_eq_zero_iff.mpr hz,mul_zero]

/-- Every upper bound valid throughout the record also bounds the
positive quadrature, even for discontinuous functions. -/
theorem average_re_le (ws : List ℝ) (f : ℝ → ℂ) (a c : ℝ)
    (h : ∀ t ∈ Set.Icc a (a+length ws), (f t).re≤c) : (average ws f a).re≤c := by
  induction ws generalizing a with
  | nil =>
    exact h a ⟨le_rfl,by simp [length]⟩
  | cons v vs ih =>
    let p := π/|v|
    have hp : 0≤p := div_nonneg pi_pos.le (abs_nonneg _)
    have hlen : length (v::vs)=p+length vs := rfl
    have hl := ih a (fun t ht => h t ⟨ht.1,ht.2.trans (by rw [hlen]; linarith only [hp])⟩)
    have hr := ih (a+p) (fun t ht => h t ⟨(le_add_of_nonneg_right hp).trans ht.1,
      ht.2.trans_eq (by rw [hlen,add_assoc])⟩)
    change ((average vs f a+average vs f (a+p))/2).re≤c
    rw [show (2:ℂ)=((2:ℝ):ℂ) by norm_num,Complex.div_ofReal_re,Complex.add_re]
    linarith only [hl,hr]

#print axioms annihilate
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
