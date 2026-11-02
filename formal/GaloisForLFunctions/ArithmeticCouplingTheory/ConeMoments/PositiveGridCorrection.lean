import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.PositiveFiniteCorrection
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import GaloisForLFunctions.RHTower.Sieve.ChordalSeparation

/-!
# Quantitative positive Fourier correction

For a finite positive frequency set, prescribed residuals with total norm at
most `A / 16` can be cancelled exactly by positive weights of mass `A`.
The nodes form an equally spaced grid above any height. If the signed spectrum
has radius `L` and separation `σ`, at most `16 |Ω| L / σ + 1` nodes suffice.
Each weight lies between `A / (2n)` and `3A / (2n)`.

The geometric-series bound makes the Fourier Gram close to the identity in
column-sum norm. Finite-dimensional injectivity supplies a solution, and its
coefficient norm controls positivity. Taking real parts preserves the symmetric
moments. Grid size is independent of residuals and translation.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- The coefficient norm controlling the pointwise size of a Fourier correction. -/
def coefficientNorm {ι : Type*} [Fintype ι] (c : ι → ℂ) : ℝ := ∑ i, ‖c i‖

lemma coefficientNorm_nonneg {ι : Type*} [Fintype ι] (c : ι → ℂ) :
    0 ≤ coefficientNorm c := sum_nonneg fun _ _ => norm_nonneg _

lemma coefficientNorm_eq_zero {ι : Type*} [Fintype ι] {c : ι → ℂ}
    (hc : coefficientNorm c = 0) : c = 0 := by
  funext i
  apply norm_eq_zero.mp
  have hi : ‖c i‖ ≤ coefficientNorm c :=
    single_le_sum (fun _ _ => norm_nonneg _) (mem_univ i)
  exact le_antisymm (hc ▸ hi) (norm_nonneg _)

lemma coefficientNorm_add_le {ι : Type*} [Fintype ι] (c d : ι → ℂ) :
    coefficientNorm (c + d) ≤ coefficientNorm c + coefficientNorm d := by
  unfold coefficientNorm
  rw [← sum_add_distrib]
  exact sum_le_sum fun i _ => norm_add_le _ _

/-- Column sums bound the Fourier Gram error in the coefficient norm. -/
lemma coefficientNorm_matrix_le {ι : Type*} [Fintype ι]
    (E : ι → ι → ℂ) {q : ℝ} (hE : ∀ j, ∑ i, ‖E i j‖ ≤ q) (c : ι → ℂ) :
    coefficientNorm (fun i => ∑ j, E i j * c j) ≤ q * coefficientNorm c := by
  calc
    _ ≤ ∑ i, ∑ j, ‖E i j‖ * ‖c j‖ := by
      apply sum_le_sum
      intro i _
      simpa only [norm_mul] using norm_sum_le (s := univ) (f := fun j => E i j * c j)
    _ = ∑ j, (∑ i, ‖E i j‖) * ‖c j‖ := by rw [sum_comm]; simp only [sum_mul]
    _ ≤ ∑ j, q * ‖c j‖ := sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hE j) (norm_nonneg _)
    _ = q * coefficientNorm c := by rw [← mul_sum]; rfl

/-- A finite Fourier system with error norm below one has a unique solution;
its displacement from a chosen baseline is controlled by the residual. -/
lemma exists_fourier_solution {ι : Type*} [Fintype ι]
    (G : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) {q : ℝ} (hq : q < 1)
    (hG : ∀ c, coefficientNorm (c - G c) ≤ q * coefficientNorm c)
    (b e : ι → ℂ) :
    ∃ c, G c = b ∧ (1-q) * coefficientNorm (c-e) ≤ coefficientNorm (b-G e) := by
  have hker : ∀ c, G c = 0 → c = 0 := by
    intro c hc
    have h := hG c
    rw [hc, sub_zero] at h
    have h0 := coefficientNorm_nonneg c
    apply coefficientNorm_eq_zero
    nlinarith only [h, h0, hq]
  have hinj : Function.Injective G := by
    intro c d hcd
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, hcd, sub_self]
  obtain ⟨c, hc⟩ := LinearMap.injective_iff_surjective.mp hinj b
  refine ⟨c, hc, ?_⟩
  have h := hG (c-e)
  have he : c-e = (c-e-G (c-e)) + G (c-e) := by abel
  have hb := coefficientNorm_add_le (c-e-G (c-e)) (G (c-e))
  rw [← he, map_sub, hc] at hb
  rw [map_sub, hc] at h
  linarith only [h, hb]

def gridMean {n : ℕ} (x : Fin n → ℝ) (u : ℝ) : ℂ :=
  (∑ j, phase u (x j)) / (n : ℂ)

def gridSynthesis {n : ℕ} {Ω : Finset ℝ} (x : Fin n → ℝ) (c : Ω → ℂ)
    (j : Fin n) : ℂ := (∑ u, c u * phase (-u.val) (x j)) / (n : ℂ)

def gridGram {n : ℕ} (Ω : Finset ℝ) (x : Fin n → ℝ) :
    (Ω → ℂ) →ₗ[ℂ] (Ω → ℂ) where
  toFun c u := ∑ v, gridMean x (u.val-v.val) * c v
  map_add' c d := by
    funext u
    simp only [Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' a c := by
    funext u
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_sum]
    apply sum_congr rfl
    intro v _
    ring

lemma gridSynthesis_moment {n : ℕ} {Ω : Finset ℝ} (x : Fin n → ℝ)
    (c : Ω → ℂ) (u : Ω) :
    ∑ j, gridSynthesis x c j * phase u.val (x j) = gridGram Ω x c u := by
  change (∑ j, ((∑ v, c v * phase (-v.val) (x j)) / (n : ℂ)) * phase u.val (x j)) =
    ∑ v, ((∑ j, phase (u.val-v.val) (x j)) / (n : ℂ)) * c v
  simp_rw [div_mul_eq_mul_div, sum_mul, ← sum_div]
  rw [sum_comm]
  apply congrArg (fun a : ℂ => a / (n : ℂ))
  apply sum_congr rfl
  intro v _
  apply sum_congr rfl
  intro j _
  rw [sub_eq_add_neg, phase_freq_add]
  ring

lemma norm_gridSynthesis_le {n : ℕ} {Ω : Finset ℝ} (x : Fin n → ℝ)
    (c : Ω → ℂ) (j : Fin n) :
    ‖gridSynthesis x c j‖ ≤ coefficientNorm c / n := by
  rw [gridSynthesis, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  calc
    _ ≤ ∑ u, ‖c u * phase (-u.val) (x j)‖ := norm_sum_le _ _
    _ = coefficientNorm c := by simp only [norm_mul, phase_norm, mul_one, coefficientNorm]

lemma gridGram_error_bound {n : ℕ} (Ω : Finset ℝ) (x : Fin n → ℝ) {q : ℝ}
    (hcol : ∀ v : Ω, ∑ u : Ω, ‖(if u=v then 1 else 0) - gridMean x (u.val-v.val)‖ ≤ q)
    (c : Ω → ℂ) : coefficientNorm (c-gridGram Ω x c) ≤ q * coefficientNorm c := by
  classical
  have he : c-gridGram Ω x c = fun u =>
      ∑ v : Ω, ((if u=v then 1 else 0) - gridMean x (u.val-v.val)) * c v := by
    funext u
    simp only [Pi.sub_apply, gridGram, LinearMap.coe_mk, AddHom.coe_mk, sub_mul, sum_sub_distrib]
    simp
  rw [he]
  exact coefficientNorm_matrix_le _ hcol c

lemma real_weights_moment {n : ℕ} (x : Fin n → ℝ) (v : Fin n → ℂ) (u : ℝ) :
    ∑ j, ((v j).re : ℂ) * phase u (x j) =
      ((∑ j, v j * phase u (x j)) + star (∑ j, v j * phase (-u) (x j))) / 2 := by
  have he : ∀ j, ((v j).re : ℂ) * phase u (x j) =
      (v j * phase u (x j) + star (v j * phase (-u) (x j))) / 2 := by
    intro j
    rw [Complex.re_eq_add_conj]
    change ((v j + star (v j)) / 2) * _ = _
    rw [star_mul, phase_neg, star_star]
    ring
  simp_rw [he]
  rw [← sum_div, sum_add_distrib, star_sum]

lemma gridSynthesis_sub {n : ℕ} {Ω : Finset ℝ} (x : Fin n → ℝ) (c e : Ω → ℂ)
    (j : Fin n) : gridSynthesis x (c-e) j = gridSynthesis x c j-gridSynthesis x e j := by
  simp only [gridSynthesis, Pi.sub_apply, sub_mul, sum_sub_distrib, sub_div]

/-- A nearly orthogonal Fourier grid realizes small symmetric moment corrections
with all weights between one half and three halves of their common baseline. -/
theorem exists_positive_frame_weights {n : ℕ} (hn : 0 < n) (Ω : Finset ℝ)
    (x : Fin n → ℝ) (u₀ : Ω) (hu₀ : u₀.val=0)
    (hneg : ∀ u ∈ Ω, -u ∈ Ω)
    (hcol : ∀ v : Ω, ∑ u : Ω,
      ‖(if u=v then 1 else 0)-gridMean x (u.val-v.val)‖ ≤ 1/8)
    {A : ℝ} (hA : 0 < A) (b : Ω → ℂ)
    (hsym : ∀ u : Ω, b ⟨-u.val, hneg u.val u.property⟩ = star (b u))
    (hsmall : coefficientNorm (b-(fun u => if u=u₀ then (A : ℂ) else 0)) ≤ A/8) :
    ∃ w : Fin n → ℝ,
      (∀ j, A/(2*n) ≤ w j ∧ w j ≤ 3*A/(2*n)) ∧
      (∀ u : Ω, ∑ j, (w j : ℂ)*phase u.val (x j)=b u) := by
  classical
  let e : Ω → ℂ := (fun u => if u=u₀ then (A : ℂ) else 0)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have heNorm : coefficientNorm e=A := by
    have he : (fun u => ‖e u‖)=(fun u => if u=u₀ then A else 0) := by
      funext u
      by_cases hu : u=u₀ <;> simp [e, hu, Complex.norm_real, abs_of_pos hA]
    rw [coefficientNorm, he]
    simp
  have heSynth : ∀ j, gridSynthesis x e j=(A : ℂ)/n := by
    intro j
    simp [gridSynthesis, e, hu₀, phase_zero]
  have hG := gridGram_error_bound Ω x hcol
  obtain ⟨c, hc, hbound⟩ := exists_fourier_solution (gridGram Ω x) (by norm_num : (1/8:ℝ)<1)
    hG b e
  have hbase : coefficientNorm (e-gridGram Ω x e) ≤ A/8 := by
    simpa only [heNorm, one_div, inv_mul_eq_div] using hG e
  have hr : coefficientNorm (b-gridGram Ω x e) ≤ A/4 := by
    have heq : b-gridGram Ω x e=(b-e)+(e-gridGram Ω x e) := by abel
    rw [heq]
    exact (coefficientNorm_add_le _ _).trans (by linarith only [hsmall, hbase])
  have hce : coefficientNorm (c-e) ≤ A/2 := by linarith only [hbound, hr, hA]
  let w : Fin n → ℝ := fun j => (gridSynthesis x c j).re
  refine ⟨w, ?_, ?_⟩
  · intro j
    have hnorm := (norm_gridSynthesis_le x (c-e) j).trans
      (div_le_div_of_nonneg_right hce hnR.le)
    rw [gridSynthesis_sub, heSynth] at hnorm
    have hre := (Complex.abs_re_le_norm (gridSynthesis x c j-(A : ℂ)/n)).trans hnorm
    have hre' : |w j-A/n| ≤ A/2/n := by
      simpa only [Complex.sub_re, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
        Complex.ofReal_re, w] using hre
    have h := abs_le.mp hre'
    have hhalf : A/2/(n : ℝ)=(A/(n : ℝ))/2 := by ring
    have hhalf' : A/(2*(n : ℝ))=(A/(n : ℝ))/2 := by ring
    have hthree : 3*A/(2*(n : ℝ))=3*(A/(n : ℝ))/2 := by ring
    rw [hhalf] at h
    constructor
    · rw [hhalf']
      linarith only [h.1]
    · rw [hthree]
      linarith only [h.2]
  · intro u
    rw [show (fun j => (w j : ℂ)*phase u.val (x j)) =
      (fun j => ((gridSynthesis x c j).re : ℂ)*phase u.val (x j)) from rfl,
      real_weights_moment]
    have hpos := gridSynthesis_moment x c u
    let v : Ω := ⟨-u.val, hneg u.val u.property⟩
    have hneg' := gridSynthesis_moment x c v
    rw [hc] at hpos hneg'
    rw [hpos, hneg', hsym, star_star]
    ring

lemma norm_phase_sub_one_abs (u h : ℝ) : ‖phase |u| h-1‖=‖phase u h-1‖ := by
  by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu]
  · rw [abs_of_neg (lt_of_not_ge hu), phase_neg]
    calc ‖star (phase u h)-1‖=‖star (phase u h-1)‖ := by rw [star_sub, star_one]
         _=‖phase u h-1‖ := norm_star _

/-- The sampling step prevents aliasing throughout the chosen frequency interval. -/
lemma grid_chord_lower {L : ℝ} (hL : 0 < L) {u : ℝ} (hu : |u| ≤ 2*L) :
    |u|/L ≤ ‖phase u (Real.pi/(2*L))-1‖ := by
  have hα0 : 0 ≤ |u|/(4*L) := div_nonneg (abs_nonneg _) (by positivity)
  have hα1 : |u|/(4*L) ≤ 1/2 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hu])
  have h := RHTower.Sieve.four_mul_le_norm_exp_two_pi_I_sub_one hα0 hα1
  have hleft : 4*(|u|/(4*L))=|u|/L := by ring
  have hright : 2*Real.pi*(|u|/(4*L))=|u| * (Real.pi/(2*L)) := by ring
  rw [hleft, hright] at h
  rw [← norm_phase_sub_one_abs u]
  exact h

lemma phase_nat_mul (u h : ℝ) (j : ℕ) : phase u (j*h)=(phase u h)^j := by
  rw [phase, phase, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- A translated frequency grid has the same geometric cancellation bound at every height. -/
lemma norm_grid_sum_le {L σ : ℝ} (hL : 0 < L) (hσ : 0 < σ) {u : ℝ}
    (hu : |u| ≤ 2*L) (hsep : σ ≤ |u|) (H : ℝ) (n : ℕ) :
    ‖∑ j : Fin n, phase u (H+j.val*(Real.pi/(2*L)))‖ ≤ 2*L/σ := by
  let h := Real.pi/(2*L)
  have hlower : σ/L ≤ ‖phase u h-1‖ :=
    (div_le_div_of_nonneg_right hsep hL.le).trans (grid_chord_lower hL hu)
  have hne : phase u h ≠ 1 := by
    intro heq
    rw [heq, sub_self, norm_zero] at hlower
    exact (not_le_of_gt (div_pos hσ hL)) hlower
  have hb := RHTower.Sieve.norm_geom_sum_le (le_of_eq (phase_norm u h)) hne n
  have he : (∑ j : Fin n, phase u (H+j.val*h)) =
      phase u H * ∑ j ∈ range n, (phase u h)^j := by
    simp_rw [phase_add, phase_nat_mul]
    rw [← mul_sum, Fin.sum_univ_eq_sum_range]
  rw [he, norm_mul, phase_norm, one_mul]
  calc
    _ ≤ 2/‖phase u h-1‖ := hb
    _ ≤ 2/(σ/L) := div_le_div_of_nonneg_left (by norm_num) (div_pos hσ hL) hlower
    _ = 2*L/σ := by field_simp

lemma gridMean_zero {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) : gridMean x 0=1 := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [gridMean, phase_zero, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self hnC

lemma norm_gridMean_le {n : ℕ} {L σ : ℝ} (hL : 0 < L) (hσ : 0 < σ)
    {u : ℝ} (hu : |u| ≤ 2*L) (hsep : σ ≤ |u|) (H : ℝ) :
    ‖gridMean (fun j : Fin n => H+j.val*(Real.pi/(2*L))) u‖ ≤ 2*L/(σ*n) := by
  rw [gridMean, norm_div, Complex.norm_natCast]
  exact (div_le_div_of_nonneg_right (norm_grid_sum_le hL hσ hu hsep H n)
    (Nat.cast_nonneg n)).trans_eq (div_div _ _ _)

/-- Polynomially many equally spaced nodes make the Fourier Gram uniformly close to identity. -/
lemma grid_column_error {n : ℕ} (hn : 0 < n) (Ω : Finset ℝ) {L σ : ℝ}
    (hL : 0 < L) (hσ : 0 < σ) (hΩ : ∀ u ∈ Ω, |u| ≤ L)
    (hsep : ∀ u ∈ Ω, ∀ v ∈ Ω, u ≠ v → σ ≤ |u-v|)
    (hnsize : 16*(Ω.card : ℝ)*L ≤ (n : ℝ)*σ) (H : ℝ) (v : Ω) :
    ∑ u : Ω, ‖(if u=v then 1 else 0)-
      gridMean (fun j : Fin n => H+j.val*(Real.pi/(2*L))) (u.val-v.val)‖ ≤ 1/8 := by
  classical
  have hbound : ∀ u : Ω, ‖(if u=v then 1 else 0)-
      gridMean (fun j : Fin n => H+j.val*(Real.pi/(2*L))) (u.val-v.val)‖ ≤ 2*L/(σ*n) := by
    intro u
    by_cases huv : u=v
    · subst u
      rw [if_pos rfl, sub_self, gridMean_zero hn, sub_self, norm_zero]
      positivity
    · rw [if_neg huv, zero_sub, norm_neg]
      have huv' : u.val ≠ v.val := fun h => huv (Subtype.ext h)
      exact norm_gridMean_le hL hσ
        ((abs_sub u.val v.val).trans (by linarith only [hΩ u.val u.property, hΩ v.val v.property]))
        (hsep u.val u.property v.val v.property huv') H
  calc
    _ ≤ ∑ _u : Ω, 2*L/(σ*n) := sum_le_sum fun u _ => hbound u
    _ = (Ω.card : ℝ)*(2*L/(σ*n)) := by simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ 1/8 := by
      have hden : 0 < σ*(n : ℝ) := mul_pos hσ (by exact_mod_cast hn)
      rw [← mul_div_assoc, div_le_iff₀ hden]
      nlinarith only [hnsize]

/-- A fixed polynomial-sized grid realizes every sufficiently small symmetric correction,
with positive weights uniformly comparable to the prescribed mean mass. -/
theorem exists_positive_grid_weights {n : ℕ} (hn : 0 < n) (Ω : Finset ℝ)
    (u₀ : Ω) (hu₀ : u₀.val=0) (hneg : ∀ u ∈ Ω, -u ∈ Ω) {L σ : ℝ}
    (hL : 0 < L) (hσ : 0 < σ) (hΩ : ∀ u ∈ Ω, |u| ≤ L)
    (hsep : ∀ u ∈ Ω, ∀ v ∈ Ω, u ≠ v → σ ≤ |u-v|)
    (hnsize : 16*(Ω.card : ℝ)*L ≤ (n : ℝ)*σ)
    {A : ℝ} (hA : 0 < A) (b : Ω → ℂ)
    (hsym : ∀ u : Ω, b ⟨-u.val, hneg u.val u.property⟩=star (b u))
    (hsmall : coefficientNorm (b-(fun u => if u=u₀ then (A : ℂ) else 0)) ≤ A/8)
    (H : ℝ) :
    ∃ w : Fin n → ℝ,
      (∀ j, A/(2*n) ≤ w j ∧ w j ≤ 3*A/(2*n)) ∧
      (∀ u : Ω, ∑ j, (w j : ℂ)*phase u.val (H+j.val*(Real.pi/(2*L)))=b u) :=
  exists_positive_frame_weights hn Ω _ u₀ hu₀ hneg
    (grid_column_error hn Ω hL hσ hΩ hsep hnsize H) hA b hsym hsmall

/-- Exact positive Fourier correction uses at most `16 |Ω| L / σ + 1` grid nodes,
uniformly over all translations. -/
theorem exists_positive_bounded_grid (Ω : Finset ℝ)
    (u₀ : Ω) (hu₀ : u₀.val=0) (hneg : ∀ u ∈ Ω, -u ∈ Ω) {L σ : ℝ}
    (hL : 0 < L) (hσ : 0 < σ) (hΩ : ∀ u ∈ Ω, |u| ≤ L)
    (hsep : ∀ u ∈ Ω, ∀ v ∈ Ω, u ≠ v → σ ≤ |u-v|) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ 16*(Ω.card : ℝ)*L/σ+1 ∧
      ∀ (A : ℝ), 0 < A → ∀ b : Ω → ℂ,
      (∀ u : Ω, b ⟨-u.val, hneg u.val u.property⟩=star (b u)) →
      coefficientNorm (b-(fun u => if u=u₀ then (A : ℂ) else 0)) ≤ A/8 →
      ∀ H : ℝ, ∃ w : Fin n → ℝ,
        (∀ j, A/(2*n) ≤ w j ∧ w j ≤ 3*A/(2*n)) ∧
        (∀ u : Ω, ∑ j, (w j : ℂ)*phase u.val (H+j.val*(Real.pi/(2*L)))=b u) := by
  classical
  let B : ℝ := 16*(Ω.card : ℝ)*L/σ
  have hcard : 0 < (Ω.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr ⟨u₀.val, u₀.property⟩)
  have hB : 0 < B := div_pos (mul_pos (mul_pos (by norm_num) hcard) hL) hσ
  let n : ℕ := ⌈B⌉₊
  have hn : 0 < n := Nat.ceil_pos.mpr hB
  have hnsize : 16*(Ω.card : ℝ)*L ≤ (n : ℝ)*σ :=
    (div_le_iff₀ hσ).mp (Nat.le_ceil B)
  refine ⟨n, hn, (Nat.ceil_lt_add_one hB.le).le, ?_⟩
  intro A hA b hsym hsmall H
  exact exists_positive_grid_weights hn Ω u₀ hu₀ hneg hL hσ hΩ hsep hnsize hA b hsym hsmall H

/-- Positive frequencies together with their negatives and the mass coordinate. -/
def symmetricSpectrum (S : Finset ℝ) : Finset ℝ := insert 0 (S ∪ S.image Neg.neg)

lemma symmetricSpectrum_neg (S : Finset ℝ) :
    ∀ u ∈ symmetricSpectrum S, -u ∈ symmetricSpectrum S := by
  classical
  intro u hu
  rcases mem_insert.mp hu with rfl | hu
  · simp [symmetricSpectrum]
  rcases mem_union.mp hu with hu | hu
  · exact mem_insert_of_mem (mem_union_right _ (mem_image.mpr ⟨u, hu, rfl⟩))
  · obtain ⟨v, hv, rfl⟩ := mem_image.mp hu
    exact mem_insert_of_mem (mem_union_left _ (by simpa only [neg_neg] using hv))

def correctionTarget (r : ℝ → ℂ) (A : ℝ) (u : ℝ) : ℂ :=
  if u=0 then (A : ℂ) else if 0 < u then -r u else -star (r (-u))

lemma correctionTarget_neg (r : ℝ → ℂ) (A u : ℝ) :
    correctionTarget r A (-u)=star (correctionTarget r A u) := by
  by_cases h0 : u=0
  · subst u
    simp [correctionTarget]
  by_cases hp : 0 < u
  · have hn : ¬0 < -u := not_lt.mpr (neg_nonpos.mpr hp.le)
    simp [correctionTarget, h0, hp, hn, neg_ne_zero.mpr h0]
  · have hn : 0 < -u := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) h0)
    simp [correctionTarget, h0, hp, hn, neg_ne_zero.mpr h0]

lemma correctionTarget_norm (r : ℝ → ℂ) (A u : ℝ) :
    ‖correctionTarget r A u-(if u=0 then (A : ℂ) else 0)‖ =
      if u=0 then 0 else ‖r |u|‖ := by
  by_cases h0 : u=0
  · subst u
    simp [correctionTarget]
  by_cases hp : 0 < u
  · simp [correctionTarget, h0, hp, abs_of_pos hp]
  · have hn : u < 0 := lt_of_le_of_ne (le_of_not_gt hp) h0
    simp [correctionTarget, h0, hp, abs_of_neg hn]

lemma correctionTarget_small (S : Finset ℝ) (hS : ∀ u ∈ S, 0 < u)
    (r : ℝ → ℂ) (A : ℝ) :
    coefficientNorm (fun u : symmetricSpectrum S => correctionTarget r A u.val-
      (if u.val=0 then (A : ℂ) else 0))=2*∑ u ∈ S, ‖r u‖ := by
  classical
  unfold coefficientNorm
  simp_rw [correctionTarget_norm]
  change (∑ u ∈ (symmetricSpectrum S).attach, if u.val=0 then 0 else ‖r |u.val|‖) = _
  rw [Finset.sum_attach (s := symmetricSpectrum S) (f := fun u : ℝ => if u=0 then 0 else ‖r |u|‖)]
  have h0S : (0 : ℝ) ∉ S := fun h => (hS 0 h).false
  have h0neg : (0 : ℝ) ∉ S.image Neg.neg := by
    intro h
    obtain ⟨v, hv, he⟩ := mem_image.mp h
    exact h0S (by simpa only [neg_eq_zero.mp he] using hv)
  have hd : Disjoint S (S.image Neg.neg) := by
    apply disjoint_left.mpr
    intro u hu hneg
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hneg
    linarith only [hS (-v) hu, hS v hv]
  have h0U : (0 : ℝ) ∉ S ∪ S.image Neg.neg := fun h => (mem_union.mp h).elim h0S h0neg
  rw [symmetricSpectrum, sum_insert h0U, if_pos rfl, zero_add,
    sum_union hd, sum_image (fun a _ b _ hab => neg_injective hab)]
  have hpos : (∑ u ∈ S, if u=0 then 0 else ‖r |u|‖) = ∑ u ∈ S, ‖r u‖ := by
    apply sum_congr rfl
    intro u hu
    rw [if_neg (hS u hu).ne', abs_of_pos (hS u hu)]
  have hneg : (∑ u ∈ S, if -u=0 then 0 else ‖r |-u|‖) = ∑ u ∈ S, ‖r u‖ := by
    apply sum_congr rfl
    intro u hu
    rw [if_neg (neg_ne_zero.mpr (hS u hu).ne'), abs_neg, abs_of_pos (hS u hu)]
  rw [hpos, hneg]
  ring

/-- Small residuals on positive frequencies admit exact positive correction on a
translated grid with polynomially bounded cardinality and length. -/
theorem exists_positive_grid_correction (S : Finset ℝ) (hS : ∀ u ∈ S, 0 < u)
    {L σ : ℝ} (hL : 0 < L) (hσ : 0 < σ)
    (hΩ : ∀ u ∈ symmetricSpectrum S, |u| ≤ L)
    (hsep : ∀ u ∈ symmetricSpectrum S, ∀ v ∈ symmetricSpectrum S,
      u ≠ v → σ ≤ |u-v|) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ 16*((symmetricSpectrum S).card : ℝ)*L/σ+1 ∧
      ∀ (A : ℝ), 0 < A → ∀ r : ℝ → ℂ, (∑ u ∈ S, ‖r u‖) ≤ A/16 →
      ∀ H : ℝ, ∃ w : Fin n → ℝ,
        (∀ j, 0 < w j ∧ A/(2*n) ≤ w j ∧ w j ≤ 3*A/(2*n)) ∧
        (∑ j, w j=A) ∧
        (∀ u ∈ S, ∑ j, (w j : ℂ)*phase u (H+j.val*(Real.pi/(2*L))) = -r u) := by
  classical
  let u₀ : symmetricSpectrum S := ⟨0, mem_insert_self _ _⟩
  obtain ⟨n, hn, hnsize, hgrid⟩ := exists_positive_bounded_grid (symmetricSpectrum S) u₀ rfl
    (symmetricSpectrum_neg S) hL hσ hΩ hsep
  refine ⟨n, hn, hnsize, ?_⟩
  intro A hA r hr H
  let b : symmetricSpectrum S → ℂ := fun u => correctionTarget r A u.val
  have hsym : ∀ u : symmetricSpectrum S,
      b ⟨-u.val, symmetricSpectrum_neg S u.val u.property⟩=star (b u) :=
    fun u => correctionTarget_neg r A u.val
  have hsmall : coefficientNorm (b-(fun u => if u=u₀ then (A : ℂ) else 0)) ≤ A/8 := by
    have he : ∀ u : symmetricSpectrum S, u=u₀ ↔ u.val=0 :=
      fun u => Subtype.ext_iff
    change coefficientNorm (fun u => correctionTarget r A u.val-
      (if u=u₀ then (A : ℂ) else 0)) ≤ A/8
    simp_rw [he]
    rw [correctionTarget_small S hS]
    linarith only [hr]
  obtain ⟨w, hw, hm⟩ := hgrid A hA b hsym hsmall H
  refine ⟨w, ?_, ?_, ?_⟩
  · intro j
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact ⟨(div_pos hA (mul_pos (by norm_num) hnR)).trans_le (hw j).1, hw j⟩
  · apply Complex.ofReal_injective
    rw [Complex.ofReal_sum]
    simpa only [u₀, b, correctionTarget, if_pos rfl, phase_zero, mul_one] using hm u₀
  · intro u hu
    let v : symmetricSpectrum S := ⟨u, mem_insert_of_mem (mem_union_left _ hu)⟩
    have h := hm v
    simpa only [v, b, correctionTarget, if_neg (hS u hu).ne', if_pos (hS u hu)] using h

#print axioms exists_positive_grid_correction
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
