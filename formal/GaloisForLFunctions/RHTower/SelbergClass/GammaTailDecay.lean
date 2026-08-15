import GaloisForLFunctions.RHTower.SelbergClass.AsymmetricFunctionalEquation
import GaloisForLFunctions.HTGeometry.GammaVerticalStripDecay

/-!
# Fixed-height decay for a Selberg Gamma pair

This module isolates the archimedean estimate needed on the vertical ray
`s + κ (-K + iv)`, `K ≤ v`.  The lower-tail parameter is `K` throughout:
there is no substitution of a later truncation height for `K`.

The result concerns one actual pair of Gamma factors in `asymmetricH`.  It
does not assert a bound for the full functional-equation factor, a contour
shift, or analytic continuation.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A point on the upward vertical side of the Selberg-twist source rectangle. -/
def selbergSourceL3Point (s : ℂ) (κ K v : ℝ) : ℂ :=
  s + (κ : ℂ) * (-(K : ℂ) + (v : ℂ) * I)

theorem selbergSourceL3Point_re (s : ℂ) (κ K v : ℝ) :
    (selbergSourceL3Point s κ K v).re = s.re - κ * K := by
  simp [selbergSourceL3Point, Complex.mul_re]
  ring

theorem selbergSourceL3Point_im (s : ℂ) (κ K v : ℝ) :
    (selbergSourceL3Point s κ K v).im = s.im + κ * v := by
  simp [selbergSourceL3Point, Complex.mul_im]

/-!
`GammaVerticalStripDecay` starts in a positive real strip.  The following
finite recurrence reduction is kept private: it is used only to treat the
fixed real parts of the two concrete Selberg Gamma arguments below.
-/
private theorem exists_bound_norm_Gamma_vertical_any_re (a : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖
        ≤ C * |t| ^ N * Real.exp (-(Real.pi * |t| / 2)) := by
  let m : ℕ := ⌈-a⌉₊ + 1
  have hceil : -a ≤ (⌈-a⌉₊ : ℝ) := Nat.le_ceil (-a)
  have hmreal : (m : ℝ) = (⌈-a⌉₊ : ℝ) + 1 := by
    simp [m]
  have hapos : 0 < a + (m : ℝ) := by
    rw [hmreal]
    linarith
  obtain ⟨C, N, hC, hbound⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip
      (a := a + (m : ℝ)) hapos (a + (m : ℝ))
  refine ⟨C, N, hC, ?_⟩
  intro t ht
  set z : ℂ := (a : ℂ) + (t : ℂ) * I with hz
  have htpos : 0 < |t| := lt_of_lt_of_le zero_lt_one ht
  have hne : ∀ i : ℕ, i < m → z + (i : ℂ) ≠ 0 := by
    intro i _ hzero
    have him : (z + (i : ℂ)).im = t := by
      rw [hz]
      simp
    rw [hzero] at him
    simp only [Complex.zero_im] at him
    rw [← him] at ht
    norm_num at ht
  have hprod := GaloisForLFunctions.HTGeometry.norm_Gamma_add_nat z m hne
  have hfac : ∀ i ∈ Finset.range m, 1 ≤ ‖z + (i : ℂ)‖ := by
    intro i _
    calc 1 ≤ |t| := ht
      _ = |(z + (i : ℂ)).im| := by
        rw [hz]
        simp
      _ ≤ ‖z + (i : ℂ)‖ := Complex.abs_im_le_norm _
  have hprod_one : 1 ≤ ∏ i ∈ Finset.range m, ‖z + (i : ℂ)‖ := by
    calc 1 = ∏ _i ∈ Finset.range m, (1 : ℝ) := by simp
      _ ≤ ∏ i ∈ Finset.range m, ‖z + (i : ℂ)‖ :=
        Finset.prod_le_prod (fun _ _ ↦ zero_le_one) hfac
  have hshift : ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + (m : ℂ))‖ := by
    rw [hprod]
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hprod_one (norm_nonneg (Complex.Gamma z)))
  have hshape : z + (m : ℂ) = ((a + (m : ℝ) : ℝ) : ℂ) + (t : ℂ) * I := by
    rw [hz]
    push_cast
    ring
  rw [hshape] at hshift
  exact hshift.trans (hbound (a + (m : ℝ)) t le_rfl le_rfl ht)

private theorem sourceL3_ordinate_bounds
    (G : SelbergGammaData) (j : Fin G.rank) (s : ℂ) {κ K v : ℝ}
    (hκ : 0 < κ)
    (hheight : 2 * (G.lambda j * |s.im| + |(G.mu j).im| + 1)
      ≤ G.lambda j * κ * K)
    (hv : K ≤ v) :
    1 ≤ |G.lambda j * (s.im + κ * v) + (G.mu j).im| ∧
      G.lambda j * κ * v / 2 ≤ |G.lambda j * (s.im + κ * v) + (G.mu j).im| ∧
      |G.lambda j * (s.im + κ * v) + (G.mu j).im|
        ≤ 2 * G.lambda j * κ * v := by
  set L : ℝ := G.lambda j
  set A : ℝ := L * |s.im| + |(G.mu j).im|
  set y : ℝ := L * (s.im + κ * v) + (G.mu j).im
  have hL : 0 < L := by simpa [L] using G.lambda_pos j
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hq : 0 < L * κ := mul_pos hL hκ
  have hheight' : 2 * (A + 1) ≤ L * κ * K := by
    simpa [A, L] using hheight
  have hleft : 0 < 2 * (A + 1) := by nlinarith
  have hqKpos : 0 < (L * κ) * K := by
    simpa [mul_assoc] using lt_of_lt_of_le hleft hheight'
  have hK : 0 < K := pos_of_mul_pos_right hqKpos hq.le
  have hvpos : 0 < v := lt_of_lt_of_le hK hv
  have hqv : 0 ≤ L * κ * v := by positivity
  have hqKle : L * κ * K ≤ L * κ * v :=
    mul_le_mul_of_nonneg_left hv hq.le
  have hhalf : A + 1 ≤ L * κ * v / 2 := by
    nlinarith [hheight', hqKle]
  have hbase : |L * s.im + (G.mu j).im| ≤ A := by
    calc |L * s.im + (G.mu j).im|
        ≤ |L * s.im| + |(G.mu j).im| := abs_add_le _ _
      _ = A := by
        rw [abs_mul, abs_of_pos hL]
  have hsplit : L * κ * v = y - (L * s.im + (G.mu j).im) := by
    dsimp [y]
    ring
  have hlow0 : L * κ * v - A ≤ |y| := by
    have habs : |L * κ * v| ≤ |y| + |L * s.im + (G.mu j).im| := by
      calc |L * κ * v| = |y - (L * s.im + (G.mu j).im)| := by rw [← hsplit]
        _ ≤ |y - 0| + |0 - (L * s.im + (G.mu j).im)| := abs_sub_le _ _ _
        _ = |y| + |L * s.im + (G.mu j).im| := by
          rw [sub_zero, zero_sub, abs_neg]
    rw [abs_of_nonneg hqv] at habs
    linarith
  have hupper0 : |y| ≤ A + L * κ * v := by
    calc |y| = |(L * s.im + (G.mu j).im) + L * κ * v| := by
          congr 1
          dsimp [y]
          ring
      _ ≤ |L * s.im + (G.mu j).im| + |L * κ * v| := abs_add_le _ _
      _ ≤ A + L * κ * v := by rw [abs_of_nonneg hqv]; gcongr
  have hlower : L * κ * v / 2 ≤ |y| := by linarith
  have hone : 1 ≤ |y| := by nlinarith
  have hupper : |y| ≤ 2 * L * κ * v := by nlinarith
  simpa [L, y] using ⟨hone, hlower, hupper⟩

private theorem first_asymmetricGamma_sourceL3_re
    (G : SelbergGammaData) (j : Fin G.rank) (s : ℂ) (κ K v : ℝ) :
    ((G.lambda j : ℂ) * (1 - selbergSourceL3Point s κ K v) + star (G.mu j)).re =
      G.lambda j * (1 - s.re + κ * K) + (G.mu j).re := by
  simp only [Complex.star_def, Complex.add_re, Complex.mul_re, Complex.sub_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.conj_re]
  rw [selbergSourceL3Point_re]
  ring

private theorem first_asymmetricGamma_sourceL3_im
    (G : SelbergGammaData) (j : Fin G.rank) (s : ℂ) (κ K v : ℝ) :
    ((G.lambda j : ℂ) * (1 - selbergSourceL3Point s κ K v) + star (G.mu j)).im =
      -(G.lambda j * (s.im + κ * v) + (G.mu j).im) := by
  simp only [Complex.star_def, Complex.add_im, Complex.mul_im, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_im, Complex.conj_im,
    zero_mul, add_zero]
  rw [selbergSourceL3Point_im]
  ring

private theorem second_asymmetricGamma_sourceL3_re
    (G : SelbergGammaData) (j : Fin G.rank) (s : ℂ) (κ K v : ℝ) :
    (1 - (G.lambda j : ℂ) * selbergSourceL3Point s κ K v - G.mu j).re =
      1 - G.lambda j * (s.re - κ * K) - (G.mu j).re := by
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, zero_mul]
  rw [selbergSourceL3Point_re]
  simp

private theorem second_asymmetricGamma_sourceL3_im
    (G : SelbergGammaData) (j : Fin G.rank) (s : ℂ) (κ K v : ℝ) :
    (1 - (G.lambda j : ℂ) * selbergSourceL3Point s κ K v - G.mu j).im =
      -(G.lambda j * (s.im + κ * v) + (G.mu j).im) := by
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_im, zero_mul]
  rw [selbergSourceL3Point_im]
  ring

/--
For a fixed actual Gamma pair in `SelbergGammaData.asymmetricH`, the source-L3
tail has a polynomial-times-exponential bound under an explicit condition on
the true lower height `K`.  The condition is deliberately stated as a
separate inequality; this theorem does not claim it follows from any global
source-rectangle choice.
-/
theorem SelbergGammaData.exists_bound_norm_asymmetricGammaPair_sourceL3
    (G : SelbergGammaData) (j : Fin G.rank) (s : ℂ) {κ K : ℝ}
    (hκ : 0 < κ)
    (hheight : 2 * (G.lambda j * |s.im| + |(G.mu j).im| + 1)
      ≤ G.lambda j * κ * K) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ v : ℝ, K ≤ v →
      ‖Complex.Gamma ((G.lambda j : ℂ) * (1 - selbergSourceL3Point s κ K v) + star (G.mu j)) *
        Complex.Gamma (1 - (G.lambda j : ℂ) * selbergSourceL3Point s κ K v - G.mu j)‖
        ≤ C * (2 * G.lambda j * κ * v) ^ N *
          Real.exp (-(Real.pi * G.lambda j * κ * v / 2)) := by
  let a₁ : ℝ := G.lambda j * (1 - s.re + κ * K) + (G.mu j).re
  let a₂ : ℝ := 1 - G.lambda j * (s.re - κ * K) - (G.mu j).re
  obtain ⟨C₁, N₁, hC₁, hGamma₁⟩ := exists_bound_norm_Gamma_vertical_any_re a₁
  obtain ⟨C₂, N₂, hC₂, hGamma₂⟩ := exists_bound_norm_Gamma_vertical_any_re a₂
  refine ⟨C₁ * C₂, N₁ + N₂, mul_nonneg hC₁ hC₂, ?_⟩
  intro v hv
  set y : ℝ := G.lambda j * (s.im + κ * v) + (G.mu j).im
  set B : ℝ := 2 * G.lambda j * κ * v
  set E : ℝ := Real.exp (-(Real.pi * G.lambda j * κ * v / 4))
  obtain ⟨hone, hlower, hupper⟩ := sourceL3_ordinate_bounds G j s hκ hheight hv
  have hupper_y : |y| ≤ B := by simpa [B, y] using hupper
  have hlower_y : G.lambda j * κ * v / 2 ≤ |y| := by
    simpa [y] using hlower
  have hB : 0 ≤ B := by
    have hB_one : 1 ≤ B := by simpa [B] using hone.trans hupper
    exact zero_le_one.trans hB_one
  have hexp : Real.exp (-(Real.pi * |y| / 2)) ≤ E := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hpow₁ : |y| ^ N₁ ≤ B ^ N₁ :=
    pow_le_pow_left₀ (abs_nonneg _) hupper_y N₁
  have hpow₂ : |y| ^ N₂ ≤ B ^ N₂ :=
    pow_le_pow_left₀ (abs_nonneg _) hupper_y N₂
  have hGamma₁' :
      ‖Complex.Gamma ((G.lambda j : ℂ) * (1 - selbergSourceL3Point s κ K v) + star (G.mu j))‖
        ≤ C₁ * B ^ N₁ * E := by
    have hshape : (G.lambda j : ℂ) * (1 - selbergSourceL3Point s κ K v) + star (G.mu j) =
        (a₁ : ℂ) + ((-y : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simpa [a₁] using first_asymmetricGamma_sourceL3_re G j s κ K v
      · simpa [y] using first_asymmetricGamma_sourceL3_im G j s κ K v
    rw [hshape]
    have hline := hGamma₁ (-y) (by simpa only [abs_neg] using hone)
    simp only [abs_neg] at hline
    calc ‖Complex.Gamma ((a₁ : ℂ) + ((-y : ℝ) : ℂ) * I)‖
        ≤ C₁ * |y| ^ N₁ * Real.exp (-(Real.pi * |y| / 2)) := hline
      _ ≤ C₁ * B ^ N₁ * E := by
        have hpoly : C₁ * |y| ^ N₁ ≤ C₁ * B ^ N₁ :=
          mul_le_mul_of_nonneg_left hpow₁ hC₁
        calc
          C₁ * |y| ^ N₁ * Real.exp (-(Real.pi * |y| / 2))
              ≤ C₁ * B ^ N₁ * Real.exp (-(Real.pi * |y| / 2)) :=
                mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
          _ ≤ C₁ * B ^ N₁ * E :=
            mul_le_mul_of_nonneg_left hexp (mul_nonneg hC₁ (pow_nonneg hB _))
  have hGamma₂' :
      ‖Complex.Gamma (1 - (G.lambda j : ℂ) * selbergSourceL3Point s κ K v - G.mu j)‖
        ≤ C₂ * B ^ N₂ * E := by
    have hshape : 1 - (G.lambda j : ℂ) * selbergSourceL3Point s κ K v - G.mu j =
        (a₂ : ℂ) + ((-y : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simpa [a₂] using second_asymmetricGamma_sourceL3_re G j s κ K v
      · simpa [y] using second_asymmetricGamma_sourceL3_im G j s κ K v
    rw [hshape]
    have hline := hGamma₂ (-y) (by simpa only [abs_neg] using hone)
    simp only [abs_neg] at hline
    calc ‖Complex.Gamma ((a₂ : ℂ) + ((-y : ℝ) : ℂ) * I)‖
        ≤ C₂ * |y| ^ N₂ * Real.exp (-(Real.pi * |y| / 2)) := hline
      _ ≤ C₂ * B ^ N₂ * E := by
        have hpoly : C₂ * |y| ^ N₂ ≤ C₂ * B ^ N₂ :=
          mul_le_mul_of_nonneg_left hpow₂ hC₂
        calc
          C₂ * |y| ^ N₂ * Real.exp (-(Real.pi * |y| / 2))
              ≤ C₂ * B ^ N₂ * Real.exp (-(Real.pi * |y| / 2)) :=
                mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
          _ ≤ C₂ * B ^ N₂ * E :=
            mul_le_mul_of_nonneg_left hexp (mul_nonneg hC₂ (pow_nonneg hB _))
  calc
    ‖Complex.Gamma ((G.lambda j : ℂ) * (1 - selbergSourceL3Point s κ K v) + star (G.mu j)) *
        Complex.Gamma (1 - (G.lambda j : ℂ) * selbergSourceL3Point s κ K v - G.mu j)‖
      = ‖Complex.Gamma ((G.lambda j : ℂ) * (1 - selbergSourceL3Point s κ K v) + star (G.mu j))‖ *
          ‖Complex.Gamma (1 - (G.lambda j : ℂ) * selbergSourceL3Point s κ K v - G.mu j)‖ :=
        norm_mul _ _
    _ ≤ (C₁ * B ^ N₁ * E) * (C₂ * B ^ N₂ * E) :=
      mul_le_mul hGamma₁' hGamma₂' (norm_nonneg _) (by positivity)
    _ = (C₁ * C₂) * B ^ (N₁ + N₂) *
        Real.exp (-(Real.pi * G.lambda j * κ * v / 2)) := by
      have hEsq : E * E = Real.exp (-(Real.pi * G.lambda j * κ * v / 2)) := by
        dsimp [E]
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        (C₁ * B ^ N₁ * E) * (C₂ * B ^ N₂ * E)
            = (C₁ * C₂) * (B ^ N₁ * B ^ N₂) * (E * E) := by ring
        _ = (C₁ * C₂) * B ^ (N₁ + N₂) *
            Real.exp (-(Real.pi * G.lambda j * κ * v / 2)) := by
          rw [← pow_add, hEsq]

end
end RHTower
