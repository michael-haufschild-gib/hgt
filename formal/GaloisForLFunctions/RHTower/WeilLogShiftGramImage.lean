import GaloisForLFunctions.RHTower.WeilLogShiftFiniteGramCostGrowth
import GaloisForLFunctions.RHTower.WeilLogShiftVanishingNormalization

/-!
# Coefficient vectors and separated sums of actual finite Gram tests

An individual test is a real linear functional on the finite coefficient space.
Separating two finite point packets makes their mixed entries vanish, so sums
of their coefficient vectors are limits of coefficient vectors of single tests.
-/

open scoped BigOperators
open Filter Topology

noncomputable section
namespace RHTower

def finiteWeilGramCoefficientVector (s : Finset ℕ) (w : FiniteWeilGramTest) : s → ℝ :=
  fun i => finiteWeilGramForm s w (Pi.single i 1)

theorem finiteWeilGramCoefficientVector_pairing (s : Finset ℕ) (w : FiniteWeilGramTest)
    (c : s → ℝ) :
    finiteWeilGramForm s w c = ∑ i, finiteWeilGramCoefficientVector s w i * c i := by
  classical
  have h := congrArg (finiteWeilGramForm s w) ((Pi.basisFun ℝ s).sum_repr c)
  simpa only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply, smul_eq_mul,
    finiteWeilGramCoefficientVector, mul_comm] using h.symm

theorem finiteWeilGramCoefficientVector_apply (s : Finset ℕ) (N : ℕ)
    (x u : Fin N → ℝ) (a : NNReal) (i : s) :
    finiteWeilGramCoefficientVector s ⟨N, x, u, a⟩ i =
      -(a : ℝ) * ∑ j, ∑ k, u j * u k * pairedLogKernel (x k - x j) ((i : ℕ) + 2) := by
  classical
  have hs (y : ℝ) : finiteWeilPotential s (Pi.single i 1) y =
      pairedLogKernel y ((i : ℕ) + 2) := by simp [finiteWeilPotential, Pi.single_apply]
  simp only [finiteWeilGramCoefficientVector, finiteWeilGramForm_apply, hs]

def finiteWeilGramTestOfFinite {ι : Type} [Fintype ι]
    (x u : ι → ℝ) (a : NNReal) : FiniteWeilGramTest :=
  ⟨Fintype.card ι, x ∘ (Fintype.equivFin ι).symm,
    u ∘ (Fintype.equivFin ι).symm, a⟩

theorem finiteWeilGramCoefficientVector_ofFinite (s : Finset ℕ) {ι : Type} [Fintype ι]
    (x u : ι → ℝ) (a : NNReal) (i : s) :
    finiteWeilGramCoefficientVector s (finiteWeilGramTestOfFinite x u a) i =
      -(a : ℝ) * ∑ j, ∑ k, u j * u k * pairedLogKernel (x k - x j) ((i : ℕ) + 2) := by
  simp only [finiteWeilGramTestOfFinite, finiteWeilGramCoefficientVector_apply, Function.comp_apply]
  congr 1
  calc
    ∑ j : Fin (Fintype.card ι), ∑ k : Fin (Fintype.card ι),
        u ((Fintype.equivFin ι).symm j) * u ((Fintype.equivFin ι).symm k) *
          pairedLogKernel (x ((Fintype.equivFin ι).symm k) - x ((Fintype.equivFin ι).symm j))
            ((i : ℕ) + 2) =
        ∑ j : Fin (Fintype.card ι), ∑ k : ι,
          u ((Fintype.equivFin ι).symm j) * u k *
            pairedLogKernel (x k - x ((Fintype.equivFin ι).symm j)) ((i : ℕ) + 2) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (Fintype.equivFin ι).symm.sum_comp (fun k : ι =>
        u ((Fintype.equivFin ι).symm j) * u k *
          pairedLogKernel (x k - x ((Fintype.equivFin ι).symm j)) ((i : ℕ) + 2))
    _ = ∑ j : ι, ∑ k : ι, u j * u k * pairedLogKernel (x k - x j) ((i : ℕ) + 2) :=
      (Fintype.equivFin ι).symm.sum_comp (fun j : ι =>
        ∑ k : ι, u j * u k * pairedLogKernel (x k - x j) ((i : ℕ) + 2))

def finiteWeilGramScale (t : NNReal) : FiniteWeilGramTest → FiniteWeilGramTest
  | ⟨N, x, u, a⟩ => ⟨N, x, u, t * a⟩

theorem finiteWeilGramCoefficientVector_scale (s : Finset ℕ) (t : NNReal)
    (w : FiniteWeilGramTest) :
    finiteWeilGramCoefficientVector s (finiteWeilGramScale t w) =
      (t : ℝ) • finiteWeilGramCoefficientVector s w := by
  rcases w with ⟨N, x, u, a⟩
  funext i
  simp only [finiteWeilGramScale, finiteWeilGramCoefficientVector_apply,
    Pi.smul_apply, smul_eq_mul, NNReal.coe_mul]
  ring

def finiteWeilGramSeparatedSum : FiniteWeilGramTest → FiniteWeilGramTest → ℝ → FiniteWeilGramTest
  | ⟨_, x, u, a⟩, ⟨_, y, v, b⟩, T =>
    finiteWeilGramTestOfFinite (Sum.elim x (fun j => T + y j))
      (Sum.elim (fun i => Real.sqrt (a : ℝ) * u i) (fun j => Real.sqrt (b : ℝ) * v j)) 1

private theorem gram_image_sqrt_sum {ι : Type} [Fintype ι] (a : NNReal)
    (u : ι → ℝ) (K : ι → ι → ℝ) :
    (∑ i, ∑ j, (Real.sqrt (a : ℝ) * u i) * (Real.sqrt (a : ℝ) * u j) * K i j) =
      (a : ℝ) * ∑ i, ∑ j, u i * u j * K i j := by
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (Real.sqrt (a : ℝ) * u i) * (Real.sqrt (a : ℝ) * u j) * K i j =
        Real.sqrt (a : ℝ) ^ 2 * (u i * u j * K i j) := by ring
    _ = (a : ℝ) * (u i * u j * K i j) := by
      erw [Real.sq_sqrt a.property]
      rfl

/-- Sums of two actual Gram coefficient vectors are limits of single-test vectors. -/
theorem tendsto_finiteWeilGramCoefficientVector_separatedSum (s : Finset ℕ)
    (w z : FiniteWeilGramTest) :
    Tendsto (fun T : ℝ => finiteWeilGramCoefficientVector s (finiteWeilGramSeparatedSum w z T))
      atTop (𝓝 (finiteWeilGramCoefficientVector s w + finiteWeilGramCoefficientVector s z)) := by
  classical
  rcases w with ⟨N, x, u, a⟩
  rcases z with ⟨M, y, v, b⟩
  apply tendsto_pi_nhds.mpr
  intro q
  let cross (T : ℝ) : ℝ := ∑ i : Fin N, ∑ j : Fin M,
    (Real.sqrt (a : ℝ) * u i) * (Real.sqrt (b : ℝ) * v j) *
      pairedLogKernel (T + y j - x i) ((q : ℕ) + 2)
  have hjoin (T : ℝ) :
      finiteWeilGramCoefficientVector s
        (finiteWeilGramSeparatedSum ⟨N, x, u, a⟩ ⟨M, y, v, b⟩ T) q =
      finiteWeilGramCoefficientVector s ⟨N, x, u, a⟩ q +
        finiteWeilGramCoefficientVector s ⟨M, y, v, b⟩ q - 2 * cross T := by
    have ha := gram_image_sqrt_sum a u (fun i j => pairedLogKernel (x j - x i) ((q : ℕ) + 2))
    have hb : (∑ i : Fin M, ∑ j : Fin M,
        (Real.sqrt (b : ℝ) * v i) * (Real.sqrt (b : ℝ) * v j) *
          pairedLogKernel ((T + y j) - (T + y i)) ((q : ℕ) + 2)) =
        (b : ℝ) * ∑ i, ∑ j, v i * v j * pairedLogKernel (y j - y i) ((q : ℕ) + 2) := by
      simp_rw [show ∀ i j, (T + y j) - (T + y i) = y j - y i by intros; ring]
      exact gram_image_sqrt_sum b v _
    have hc : (∑ j : Fin M, ∑ i : Fin N,
        (Real.sqrt (b : ℝ) * v j) * (Real.sqrt (a : ℝ) * u i) *
          pairedLogKernel (x i - (T + y j)) ((q : ℕ) + 2)) = cross T := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [show x i - (T + y j) = -(T + y j - x i) by ring, pairedLogKernel_neg]
      ring
    simp only [finiteWeilGramSeparatedSum, finiteWeilGramCoefficientVector_ofFinite,
      finiteWeilGramCoefficientVector_apply, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, NNReal.coe_one, neg_one_mul, Finset.sum_add_distrib]
    rw [ha, hb, hc]
    dsimp [cross]
    ring
  have hcross : Tendsto cross atTop (𝓝 0) := by
    have hterm (i : Fin N) (j : Fin M) : Tendsto
        (fun T : ℝ => (Real.sqrt (a : ℝ) * u i) * (Real.sqrt (b : ℝ) * v j) *
          pairedLogKernel (T + y j - x i) ((q : ℕ) + 2)) atTop (𝓝 0) := by
      have hshift : Tendsto (fun T : ℝ => T + y j - x i) atTop atTop := by
        refine tendsto_atTop.mpr fun d => ?_
        filter_upwards [eventually_ge_atTop (d - y j + x i)] with T hT
        linarith
      have hp := (tendsto_pairedLogKernel_cocompact ((q : ℕ) + 2)).comp
        (hshift.mono_right atTop_le_cocompact)
      simpa only [mul_zero, Function.comp_apply] using hp.const_mul
        ((Real.sqrt (a : ℝ) * u i) * (Real.sqrt (b : ℝ) * v j))
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ => tendsto_finsetSum Finset.univ (fun j _ => hterm i j))
  simp_rw [hjoin]
  simpa only [mul_zero, sub_zero, Pi.add_apply] using
    (tendsto_const_nhds.sub (hcross.const_mul 2))

end RHTower
