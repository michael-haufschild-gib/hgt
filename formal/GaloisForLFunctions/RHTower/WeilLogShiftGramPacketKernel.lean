import GaloisForLFunctions.RHTower.WeilLogShiftGramImage
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticSurjection

/-! The quadratic amplitude map of finitely many translated actual packets.
Its mixed-packet coefficient vectors converge to a prescribed weighted diagonal. -/

open scoped BigOperators
open Filter Topology
attribute [local instance] Classical.propDecidable

noncomputable section
namespace RHTower

variable {J : Type} [Fintype J]

def finiteWeilGramPacketAmplitude (w : J → FiniteWeilGramTest) (a : J → NNReal)
    (j : J) (i : Fin (w j).1) : ℝ :=
  Real.sqrt ((a j : ℝ) * ((w j).2.2.2 : ℝ)) * (w j).2.2.1 i

def finiteWeilGramPacketNodes (w : J → FiniteWeilGramTest) (ell : J → ℝ) (T : ℝ)
    (i : Σ j, Fin (w j).1) : ℝ := T * ell i.1 + (w i.1).2.1 i.2

def finiteWeilGramPacketKernel (s : Finset ℕ) (w : J → FiniteWeilGramTest)
    (a : J → NNReal) (ell : J → ℝ) (T : ℝ) (j h : J) (k : s) : ℝ :=
  -∑ i : Fin (w j).1, ∑ l : Fin (w h).1,
    finiteWeilGramPacketAmplitude w a j i * finiteWeilGramPacketAmplitude w a h l *
      pairedLogKernel ((T * ell h + (w h).2.1 l) - (T * ell j + (w j).2.1 i))
        ((k : ℕ) + 2)

private theorem gram_coefficient_expansion (s : Finset ℕ) (z : FiniteWeilGramTest)
    (k : s) :
    finiteWeilGramCoefficientVector s z k = -(z.2.2.2 : ℝ) *
      ∑ i : Fin z.1, ∑ l : Fin z.1,
        z.2.2.1 i * z.2.2.1 l * pairedLogKernel (z.2.1 l - z.2.1 i) ((k : ℕ) + 2) := by
  rcases z with ⟨N, x, u, b⟩
  exact finiteWeilGramCoefficientVector_apply s N x u b k

omit [Fintype J] in
theorem finiteWeilGramPacketKernel_diagonal (s : Finset ℕ) (w : J → FiniteWeilGramTest)
    (a : J → NNReal) (ell : J → ℝ) (T : ℝ) (j : J) :
    finiteWeilGramPacketKernel s w a ell T j j =
      (a j : ℝ) • finiteWeilGramCoefficientVector s (w j) := by
  funext k
  let N := (w j).1
  let x : Fin N → ℝ := (w j).2.1
  let u : Fin N → ℝ := (w j).2.2.1
  let b : NNReal := (w j).2.2.2
  have hv : finiteWeilGramCoefficientVector s (w j) k =
      -(b : ℝ) * ∑ i : Fin N, ∑ l : Fin N,
        u i * u l * pairedLogKernel (x l - x i) ((k : ℕ) + 2) :=
    gram_coefficient_expansion s (w j) k
  change -(∑ i : Fin N, ∑ l : Fin N,
      (Real.sqrt ((a j : ℝ) * (b : ℝ)) * u i) *
        (Real.sqrt ((a j : ℝ) * (b : ℝ)) * u l) *
          pairedLogKernel ((T * ell j + x l) - (T * ell j + x i)) ((k : ℕ) + 2)) =
    (a j : ℝ) * finiteWeilGramCoefficientVector s (w j) k
  rw [hv]
  have hsqrt := Real.sq_sqrt (mul_nonneg (NNReal.coe_nonneg (a j)) (NNReal.coe_nonneg b))
  have hsum : (∑ i : Fin N, ∑ l : Fin N,
      (Real.sqrt ((a j : ℝ) * (b : ℝ)) * u i) *
        (Real.sqrt ((a j : ℝ) * (b : ℝ)) * u l) *
          pairedLogKernel ((T * ell j + x l) - (T * ell j + x i)) ((k : ℕ) + 2)) =
      ((a j : ℝ) * (b : ℝ)) *
        ∑ i : Fin N, ∑ l : Fin N, u i * u l * pairedLogKernel (x l - x i) ((k : ℕ) + 2) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    rw [show (T * ell j + x l) - (T * ell j + x i) = x l - x i by ring]
    calc
      _ = Real.sqrt ((a j : ℝ) * (b : ℝ)) ^ 2 *
          (u i * u l * pairedLogKernel (x l - x i) ((k : ℕ) + 2)) := by ring
      _ = _ := by rw [hsqrt]
  rw [hsum]
  ring

private theorem affine_shift_cocompact {d : ℝ} (hd : d ≠ 0) (c : ℝ) :
    Tendsto (fun T : ℝ => d * T + c) atTop (cocompact ℝ) := by
  apply tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℝ)
  refine tendsto_atTop.mpr fun b => ?_
  filter_upwards [eventually_ge_atTop (max 0 ((b + |c|) / |d|))] with T hT
  have hT0 : 0 ≤ T := (le_max_left _ _).trans hT
  have hdpos : 0 < |d| := abs_pos.mpr hd
  have hT' : (b + |c|) / |d| ≤ T := (le_max_right _ _).trans hT
  have hprod := (div_le_iff₀ hdpos).mp hT'
  have habs : |d * T| ≤ |d * T + c| + |c| := by
    simpa using abs_sub (d * T + c) c
  rw [abs_mul, abs_of_nonneg hT0] at habs
  simp only [dist_zero_right, Real.norm_eq_abs]
  nlinarith

omit [Fintype J] in
theorem tendsto_finiteWeilGramPacketKernel (s : Finset ℕ) (w : J → FiniteWeilGramTest)
    (a : J → NNReal) (ell : J → ℝ) (hell : Function.Injective ell) :
    Tendsto (finiteWeilGramPacketKernel s w a ell) atTop
      (𝓝 (finiteWeilQuadraticDiagonal (fun j =>
        (a j : ℝ) • finiteWeilGramCoefficientVector s (w j)))) := by
  apply tendsto_pi_nhds.mpr
  intro j
  apply tendsto_pi_nhds.mpr
  intro h
  by_cases hjh : j = h
  · subst h
    simp only [finiteWeilGramPacketKernel_diagonal, finiteWeilQuadraticDiagonal]
    exact tendsto_const_nhds
  · apply tendsto_pi_nhds.mpr
    intro k
    have hdiff : ell h - ell j ≠ 0 := by
      intro he
      exact hjh (hell (sub_eq_zero.mp he)).symm
    have hterm (i : Fin (w j).1) (l : Fin (w h).1) :
        Tendsto (fun T : ℝ =>
          finiteWeilGramPacketAmplitude w a j i * finiteWeilGramPacketAmplitude w a h l *
            pairedLogKernel ((T * ell h + (w h).2.1 l) -
              (T * ell j + (w j).2.1 i)) ((k : ℕ) + 2)) atTop (𝓝 0) := by
      have hs := affine_shift_cocompact hdiff ((w h).2.1 l - (w j).2.1 i)
      have heq : (fun T : ℝ => (ell h - ell j) * T + ((w h).2.1 l - (w j).2.1 i)) =
          (fun T : ℝ => (T * ell h + (w h).2.1 l) - (T * ell j + (w j).2.1 i)) := by
        funext T
        ring
      rw [heq] at hs
      have hk := (tendsto_pairedLogKernel_cocompact ((k : ℕ) + 2)).comp hs
      simpa only [mul_zero, Function.comp_apply] using hk.const_mul
        (finiteWeilGramPacketAmplitude w a j i * finiteWeilGramPacketAmplitude w a h l)
    have hsum := tendsto_finsetSum Finset.univ (fun i _ =>
      tendsto_finsetSum Finset.univ (fun l _ => hterm i l))
    simpa only [finiteWeilGramPacketKernel, finiteWeilQuadraticDiagonal, if_neg hjh,
      Pi.zero_apply, Finset.sum_const_zero, neg_zero] using hsum.neg

theorem finiteWeilGramCoefficientVector_packet (s : Finset ℕ) (w : J → FiniteWeilGramTest)
    (a : J → NNReal) (ell : J → ℝ) (T : ℝ) (t : J → ℝ) :
    finiteWeilGramCoefficientVector s
      (finiteWeilGramTestOfFinite (finiteWeilGramPacketNodes w ell T)
        (fun i : Σ j, Fin (w j).1 => t i.1 * finiteWeilGramPacketAmplitude w a i.1 i.2) 1) =
      finiteWeilQuadraticMap (finiteWeilGramPacketKernel s w a ell T) t := by
  funext k
  rw [finiteWeilGramCoefficientVector_ofFinite]
  simp only [NNReal.coe_one, neg_one_mul, finiteWeilGramPacketNodes,
    Fintype.sum_sigma, finiteWeilQuadraticMap, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    finiteWeilGramPacketKernel, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  ring

end RHTower
