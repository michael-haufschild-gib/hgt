import GaloisForLFunctions.HTGeometry.JumpProfileLevels
import GaloisForLFunctions.HTGeometry.UnimodularWindowMoments

/-!
# One window of the remainder recursion

Assigning unimodular phases with prescribed weights to a family of nodes inside a window replaces
the level vector of the remainder chain by the rounding error of the moment problem.  This is the
inductive step of an Andersson-type recursion: the Taylor image of the old levels is cancelled by
the window moments, and only the `J · C` rounding error survives, scaled by `Δ^j / j!`.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- The source built from a node family, a phase and a weight. -/
def windowAssign {N : ℕ} (p : Fin N → ℕ) (b : Fin N → ℂ) (w : Fin N → ℝ) : ℕ → ℂ :=
  fun n => if h : ∃ r, p r = n then b h.choose * ((w h.choose : ℝ) : ℂ) else 0

theorem windowAssign_apply {N : ℕ} {p : Fin N → ℕ} (hinj : Function.Injective p)
    (b : Fin N → ℂ) (w : Fin N → ℝ) (r : Fin N) :
    windowAssign p b w (p r) = b r * ((w r : ℝ) : ℂ) := by
  have hex : ∃ r', p r' = p r := ⟨r, rfl⟩
  rw [windowAssign, dif_pos hex]
  have : hex.choose = r := hinj hex.choose_spec
  rw [this]

theorem windowAssign_of_notMem {N : ℕ} (p : Fin N → ℕ) (b : Fin N → ℂ) (w : Fin N → ℝ) {n : ℕ}
    (hn : ∀ r, p r ≠ n) : windowAssign p b w n = 0 := by
  rw [windowAssign, dif_neg]
  rintro ⟨r, hr⟩
  exact hn r hr

theorem sum_windowAssign {N : ℕ} {p : Fin N → ℕ} (hinj : Function.Injective p)
    (b : Fin N → ℂ) (w : Fin N → ℝ) {S : Finset ℕ} (hp : ∀ r, p r ∈ S) (f : ℕ → ℂ) :
    (∑ n ∈ S, windowAssign p b w n * f n)
      = ∑ r : Fin N, b r * ((w r : ℝ) : ℂ) * f (p r) := by
  classical
  have himg : (Finset.univ.image p) ⊆ S := by
    intro n hn
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.1 hn
    exact hp r
  have hzero : ∀ n ∈ S, n ∉ Finset.univ.image p → windowAssign p b w n * f n = 0 := by
    intro n _ hnot
    have : ∀ r, p r ≠ n := by
      intro r hr
      exact hnot (Finset.mem_image.2 ⟨r, Finset.mem_univ r, hr⟩)
    rw [windowAssign_of_notMem p b w this, zero_mul]
  rw [← Finset.sum_subset himg hzero,
    Finset.sum_image (fun r _ r' _ h => hinj h)]
  exact Finset.sum_congr rfl fun r _ => by rw [windowAssign_apply hinj b w r]

/-- The Taylor image at `y` of the levels at the base point `x`. -/
def windowTaylor (a : ℕ → ℂ) (x y : ℝ) (j : ℕ) : ℂ :=
  ∑ m ∈ Finset.range (j + 1),
    (((y - x) ^ (j - m) / (((j - m).factorial : ℕ) : ℝ) : ℝ) : ℂ) * arithProfile a m x

/-- The moment vector the window must realize in order to cancel the Taylor image. -/
def windowTarget (a : ℕ → ℂ) (x y : ℝ) (j : ℕ) : ℂ :=
  -((((j.factorial : ℕ) : ℝ) / (y - x) ^ j : ℝ) : ℂ) * windowTaylor a x y j

/-- The window nodes normalized to `[0,1]`. -/
def windowNode {N : ℕ} (p : Fin N → ℕ) (x y : ℝ) : Fin N → ℝ :=
  fun r => (y - (p r : ℝ)) / (y - x)

theorem windowNode_mem_Icc {N : ℕ} {p : Fin N → ℕ} {x y : ℝ} (hx : 1 ≤ x) (hxy : x < y)
    (hp : ∀ r, p r ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊) (r : Fin N) :
    windowNode p x y r ∈ Set.Icc (0:ℝ) 1 := by
  have hx0 : (0:ℝ) ≤ x := le_trans zero_le_one hx
  have hy0 : (0:ℝ) ≤ y := le_trans hx0 (le_of_lt hxy)
  have hD : 0 < y - x := by linarith
  have hmem := Finset.mem_Ioc.1 (hp r)
  have hup : (p r : ℝ) ≤ y := by
    have h1 : (p r : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hmem.2
    exact le_trans h1 (Nat.floor_le hy0)
  have hlow : x < (p r : ℝ) := by
    have h1 : (⌊x⌋₊ : ℝ) + 1 ≤ (p r : ℝ) := by exact_mod_cast hmem.1
    have h2 := Nat.lt_floor_add_one x
    linarith
  constructor
  · rw [windowNode]
    exact div_nonneg (by linarith) (le_of_lt hD)
  · rw [windowNode, div_le_one hD]
    linarith

/-- **The window step.**  With enough weighted nodes in the window — a Rayleigh floor for their
moment matrix — unimodular phases can be assigned so that every level of the remainder chain at the
right endpoint is bounded by the rounding error, scaled by `Δ^j / j!`. -/
theorem exists_window_phases {N J : ℕ} (hJ : 0 < J) (a : ℕ → ℂ) {x y : ℝ} (hx : 1 ≤ x)
    (hxy : x < y) {p : Fin N → ℕ} (hinj : Function.Injective p)
    (hp : ∀ r, p r ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊) (w : Fin N → ℝ) {C : ℝ} (hC : ∀ r, |w r| ≤ C)
    (hC0 : 0 ≤ C) {lam : ℝ} (hlam : 0 < lam)
    (hquad : ∀ u : Fin J → ℝ,
      lam * (∑ i, u i ^ 2) ≤ u ⬝ᵥ (atomicHankel w (windowNode p x y) J).mulVec u)
    (hsize : (J : ℝ) * (∑ j : Fin J, ‖2 * windowTarget a x y (j : ℕ)‖ ^ 2) ≤ lam ^ 2) :
    ∃ b : Fin N → ℂ, (∀ r, ‖b r‖ = 1) ∧
      ∀ j : Fin J,
        ‖arithProfile (updateWindow a (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊) (windowAssign p b w)) (j : ℕ) y‖
          ≤ ((y - x) ^ (j : ℕ) / (((j : ℕ).factorial : ℕ) : ℝ)) * ((J : ℝ) * C) := by
  classical
  have hD : 0 < y - x := by linarith
  obtain ⟨b, hb1, hb2⟩ := exists_unimodular_window_moments_complex hJ hlam
    (windowNode p x y) w (windowNode_mem_Icc hx hxy hp) hC hC0 hquad
    (fun j => windowTarget a x y (j : ℕ)) hsize
  refine ⟨b, hb1, fun j => ?_⟩
  have hfac : (0:ℝ) < (((j : ℕ).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j : ℕ)
  have hDj : (0:ℝ) < (y - x) ^ (j : ℕ) := pow_pos hD _
  set κ : ℝ := (y - x) ^ (j : ℕ) / (((j : ℕ).factorial : ℕ) : ℝ) with hκ
  have hκpos : 0 < κ := by
    rw [hκ]
    exact div_pos hDj hfac
  have hstep := arithProfile_updateWindow_step a (windowAssign p b w) (j : ℕ) hx (le_of_lt hxy)
  have hwindow : (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, windowAssign p b w n
        * (((y - (n : ℝ)) ^ (j : ℕ) / (((j : ℕ).factorial : ℕ) : ℝ) : ℝ) : ℂ))
      = (κ : ℂ) * ∑ r : Fin N, b r * ((w r * windowNode p x y r ^ (j : ℕ) : ℝ) : ℂ) := by
    rw [sum_windowAssign hinj b w hp
      (fun n => (((y - (n : ℝ)) ^ (j : ℕ) / (((j : ℕ).factorial : ℕ) : ℝ) : ℝ) : ℂ)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hnode : (y - (p r : ℝ)) = (y - x) * windowNode p x y r := by
      rw [windowNode]
      field_simp
    rw [hnode, hκ, windowNode]
    push_cast
    rw [mul_pow]
    field_simp
  have hone : ((κ : ℝ) : ℂ)
      * (((((j : ℕ).factorial : ℕ) : ℝ) / (y - x) ^ (j : ℕ) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hκ]
    norm_cast
    field_simp
  have htaylor : (κ : ℂ) * windowTarget a x y (j : ℕ) = -windowTaylor a x y (j : ℕ) := by
    rw [windowTarget, ← mul_assoc, mul_neg, hone, neg_one_mul]
  rw [hstep, ← windowTaylor, hwindow]
  have hcollect : windowTaylor a x y (j : ℕ)
      + (κ : ℂ) * ∑ r : Fin N, b r * ((w r * windowNode p x y r ^ (j : ℕ) : ℝ) : ℂ)
      = (κ : ℂ) * ((∑ r : Fin N, b r * ((w r * windowNode p x y r ^ (j : ℕ) : ℝ) : ℂ))
          - windowTarget a x y (j : ℕ)) := by
    rw [mul_sub, htaylor]
    ring
  rw [hcollect, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκpos]
  exact mul_le_mul_of_nonneg_left (hb2 j) (le_of_lt hκpos)

theorem sum_inv_factorial_mul (j : ℕ) :
    (∑ m ∈ Finset.range (j + 1),
        (1:ℝ) / ((((j - m).factorial : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ)))
      = 2 ^ j / ((j.factorial : ℕ) : ℝ) := by
  have hfac : ((j.factorial : ℕ) : ℝ) ≠ 0 := by
    have := Nat.factorial_pos j
    positivity
  rw [eq_div_iff hfac, Finset.sum_mul]
  have hterm : ∀ m ∈ Finset.range (j + 1),
      (1:ℝ) / ((((j - m).factorial : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ))
        * ((j.factorial : ℕ) : ℝ) = ((j.choose m : ℕ) : ℝ) := by
    intro m hm
    have hmj : m ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    have hkey : ((j.choose m : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ)
        * (((j - m).factorial : ℕ) : ℝ) = ((j.factorial : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_mul_factorial_mul_factorial hmj)
    have hm0 : ((m.factorial : ℕ) : ℝ) ≠ 0 := by
      have := Nat.factorial_pos m
      positivity
    have hjm0 : (((j - m).factorial : ℕ) : ℝ) ≠ 0 := by
      have := Nat.factorial_pos (j - m)
      positivity
    field_simp
    linarith [hkey]
  rw [Finset.sum_congr rfl hterm]
  have := Nat.sum_range_choose j
  exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this

/-- **The target stays bounded.**  If the levels at the base point obey the window bound with
constant `K`, the moment the next window must realize is at most `2^j K`. -/
theorem norm_windowTarget_le {a : ℕ → ℂ} {x y : ℝ} (hxy : x < y) {K : ℝ} {j : ℕ}
    (hstate : ∀ m ≤ j, ‖arithProfile a m x‖ ≤ ((y - x) ^ m / ((m.factorial : ℕ) : ℝ)) * K) :
    ‖windowTarget a x y j‖ ≤ 2 ^ j * K := by
  have hD : 0 < y - x := by linarith
  have hfac : (0:ℝ) < ((j.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hDj : (0:ℝ) < (y - x) ^ j := pow_pos hD _
  have hK0 : 0 ≤ K := by
    have h0 := hstate 0 (Nat.zero_le j)
    have hnn : 0 ≤ ‖arithProfile a 0 x‖ := norm_nonneg _
    by_contra hcon
    push_neg at hcon
    have : ((y - x) ^ 0 / ((Nat.factorial 0 : ℕ) : ℝ)) * K < 0 := by
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
      exact hcon
    linarith
  have htaylor : ‖windowTaylor a x y j‖ ≤ K * (y - x) ^ j * (2 ^ j / ((j.factorial : ℕ) : ℝ)) := by
    have hbound : ‖windowTaylor a x y j‖
        ≤ ∑ m ∈ Finset.range (j + 1),
            ((y - x) ^ (j - m) / ((((j - m).factorial : ℕ)) : ℝ)) * ‖arithProfile a m x‖ := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m _ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine le_trans hbound ?_
    have hterm : ∀ m ∈ Finset.range (j + 1),
        ((y - x) ^ (j - m) / ((((j - m).factorial : ℕ)) : ℝ)) * ‖arithProfile a m x‖
          ≤ K * (y - x) ^ j * (1 / ((((j - m).factorial : ℕ)) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹) := by
      intro m hm
      have hmj : m ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
      have hfacm : (0:ℝ) < ((m.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
      have hfacjm : (0:ℝ) < (((j - m).factorial : ℕ) : ℝ) := by
        exact_mod_cast Nat.factorial_pos (j - m)
      have hpow : (y - x) ^ (j - m) * (y - x) ^ m = (y - x) ^ j := by
        rw [← pow_add]
        congr 1
        omega
      calc ((y - x) ^ (j - m) / ((((j - m).factorial : ℕ)) : ℝ)) * ‖arithProfile a m x‖
          ≤ ((y - x) ^ (j - m) / ((((j - m).factorial : ℕ)) : ℝ))
              * (((y - x) ^ m / ((m.factorial : ℕ) : ℝ)) * K) := by
            refine mul_le_mul_of_nonneg_left (hstate m hmj) ?_
            positivity
        _ = K * ((y - x) ^ (j - m) * (y - x) ^ m)
              * (1 / ((((j - m).factorial : ℕ)) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹) := by
            field_simp
        _ = K * (y - x) ^ j
              * (1 / ((((j - m).factorial : ℕ)) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹) := by
            rw [hpow]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hsum : (∑ m ∈ Finset.range (j + 1),
        (1 / ((((j - m).factorial : ℕ)) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹))
        = 2 ^ j / ((j.factorial : ℕ) : ℝ) := by
      rw [← sum_inv_factorial_mul j]
      refine Finset.sum_congr rfl fun m _ => ?_
      field_simp
    rw [hsum]
  have hfinal : ‖windowTarget a x y j‖
      = (((j.factorial : ℕ) : ℝ) / (y - x) ^ j) * ‖windowTaylor a x y j‖ := by
    rw [windowTarget, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  rw [hfinal]
  calc (((j.factorial : ℕ) : ℝ) / (y - x) ^ j) * ‖windowTaylor a x y j‖
      ≤ (((j.factorial : ℕ) : ℝ) / (y - x) ^ j)
          * (K * (y - x) ^ j * (2 ^ j / ((j.factorial : ℕ) : ℝ))) := by
        refine mul_le_mul_of_nonneg_left htaylor ?_
        positivity
    _ = 2 ^ j * K := by
        field_simp

end GaloisForLFunctions.HTGeometry

end
