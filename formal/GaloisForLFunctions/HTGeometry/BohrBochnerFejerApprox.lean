import GaloisForLFunctions.HTGeometry.BohrMultiFejerOperator
import GaloisForLFunctions.HTGeometry.BohrFejerPolynomial
import GaloisForLFunctions.HTGeometry.RationalBasisIntegerCombination
import GaloisForLFunctions.HTGeometry.BohrApproximation

/-!
# The Bochner–Fejér approximation theorem

Every almost periodic function is a uniform limit of trigonometric polynomials whose frequencies lie
in its **spectrum**.

The Peter–Weyl approximation theorem already gives a trigonometric approximant, but with no control
on its frequencies.  Writing that approximant over a rational base and convolving with the
multi-dimensional Fejér kernel of high enough order repairs this: the operator is a contraction, so
it moves the approximant and the function by the same small amount; it acts on the approximant
diagonally through multipliers close to one; and its output is, by the convolution formula, a
trigonometric polynomial whose coefficients carry a factor of a Bohr coefficient of the function,
hence supported on the spectrum.
-/

open Filter Topology

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- **Diagonal action on a trigonometric polynomial** whose frequencies are integer combinations of
the base. -/
theorem bohrMean_translate_trigPoly_mul_multiFejerKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → ℝ} (hind : LinearIndependent ℚ β) (N : ι → ℕ) {n : ℕ} (c : Fin n → ℂ)
    (m : Fin n → ι → ℤ) (hm : ∀ j i, (m j i).natAbs ≤ N i) (t : ℝ) :
    bohrMean (fun u => (∑ j : Fin n, c j * expChar (∑ i : ι, (m j i : ℝ) * β i) (u + t))
        * multiFejerKernel β N u)
      = ∑ j : Fin n, (c j * ((fejerMultiplier N (m j) : ℝ) : ℂ))
          * expChar (∑ i : ι, (m j i : ℝ) * β i) t := by
  classical
  have hKc : Continuous (multiFejerKernel β N) := continuous_multiFejerKernel β N
  have hKa : HTGeometry.IsBohrAlmostPeriodic (multiFejerKernel β N) :=
    isBohrAlmostPeriodic_multiFejerKernel β N
  have hcj : ∀ j : Fin n, Continuous fun u : ℝ =>
      expChar (∑ i : ι, (m j i : ℝ) * β i) (u + t) * multiFejerKernel β N u := by
    intro j
    exact ((continuous_expChar _).comp (continuous_id.add continuous_const)).mul hKc
  have haj : ∀ j : Fin n, HTGeometry.IsBohrAlmostPeriodic fun u : ℝ =>
      expChar (∑ i : ι, (m j i : ℝ) * β i) (u + t) * multiFejerKernel β N u := by
    intro j
    exact isBohrAlmostPeriodic_mul
      ((continuous_expChar _).comp (continuous_id.add continuous_const))
      (isBohrAlmostPeriodic_comp_add_const (isBohrAlmostPeriodic_expChar _) t) hKc hKa
  have hfun : (fun u => (∑ j : Fin n, c j * expChar (∑ i : ι, (m j i : ℝ) * β i) (u + t))
      * multiFejerKernel β N u)
      = fun u => ∑ j : Fin n, c j *
          (expChar (∑ i : ι, (m j i : ℝ) * β i) (u + t) * multiFejerKernel β N u) := by
    funext u
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hfun, bohrMean_sum (F := fun j : Fin n => fun u : ℝ => c j *
      (expChar (∑ i : ι, (m j i : ℝ) * β i) (u + t) * multiFejerKernel β N u)) Finset.univ
    (fun j _ => continuous_const.mul (hcj j))
    (fun j _ => isBohrAlmostPeriodic_const_mul _ (haj j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bohrMean_const_mul _ (hcj j) (haj j),
    bohrMean_translate_expChar_mul_multiFejerKernel hind N (m j) (fun i => hm j i) t]
  ring

/-- **The Bochner–Fejér approximation theorem.**  An almost periodic function is uniformly
approximated by trigonometric polynomials with frequencies in its spectrum. -/
theorem exists_trigPoly_spectrum_approx {f : ℝ →ᵇ ℂ} (hf : UniformContinuous fun x => f x)
    (htb : HasTotallyBoundedOrbit fun x => f x) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (S : Finset ℝ) (a : ℝ → ℂ), (↑S ⊆ bohrSpectrum fun x => f x) ∧
      ∀ t, ‖f t - ∑ lam ∈ S, a lam * expChar lam t‖ ≤ δ := by
  classical
  have hfc : Continuous fun x => f x := f.continuous
  have hfa : HTGeometry.IsBohrAlmostPeriodic fun x => f x :=
    isBohrAlmostPeriodic_of_hasTotallyBoundedOrbit htb
  have hδ3 : (0 : ℝ) < δ / 3 := by linarith
  obtain ⟨n, c, lam, hclose⟩ := exists_trig_approx hf htb hδ3
  obtain ⟨k, β, m, hind, hlam⟩ := exists_ratBasis_int_combination lam
  -- the approximant, rewritten over the rational base
  set P : ℝ → ℂ := fun t => ∑ j : Fin n, c j * expChar (∑ i : Fin k, (m j i : ℝ) * β i) t with hP
  have hPclose : ∀ t, ‖f t - P t‖ ≤ δ / 3 := by
    intro t
    have h := hclose t
    have hEq : (∑ j : Fin n, c j * Complex.exp ((lam j * t : ℝ) * Complex.I)) = P t := by
      rw [hP]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hlam j]
      rfl
    rw [hEq] at h
    exact h
  have hPc : Continuous P :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_expChar _)
  have hPa : HTGeometry.IsBohrAlmostPeriodic P :=
    isBohrAlmostPeriodic_sum _ (fun j _ => continuous_const.mul (continuous_expChar _))
      (fun j _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_expChar _))
  -- the orders
  set A : ℝ := ∑ j : Fin n, ‖c j‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => norm_nonneg _
  set M : ℕ := ∑ j : Fin n, ∑ i : Fin k, (m j i).natAbs with hM
  have hrow : ∀ j : Fin n, (∑ i : Fin k, (m j i).natAbs) ≤ M :=
    fun j => Finset.single_le_sum (f := fun j' : Fin n => ∑ i : Fin k, (m j' i).natAbs)
      (fun j' _ => Nat.zero_le _) (Finset.mem_univ j)
  have hentry : ∀ (j : Fin n) (i : Fin k), (m j i).natAbs ≤ M := by
    intro j i
    refine le_trans ?_ (hrow j)
    exact Finset.single_le_sum (f := fun i' : Fin k => (m j i').natAbs)
      (fun i' _ => Nat.zero_le _) (Finset.mem_univ i)
  obtain ⟨N0, hN0⟩ := exists_nat_gt (3 * A * M / δ)
  set Nmax : ℕ := max M N0 with hNmax
  set Nord : Fin k → ℕ := fun _ => Nmax with hNord
  have hmN : ∀ (j : Fin n) (i : Fin k), (m j i).natAbs ≤ Nord i :=
    fun j i => le_trans (hentry j i) (le_max_left _ _)
  have hX : (0 : ℝ) < (Nmax : ℝ) + 1 := by positivity
  -- the multiplier defect is small
  have hdefect : ∀ j : Fin n, 1 - fejerMultiplier Nord (m j) ≤ (M : ℝ) / ((Nmax : ℝ) + 1) := by
    intro j
    refine le_trans (one_sub_fejerMultiplier_le Nord (m j) (fun i => hmN j i)) ?_
    have hsum : ∑ i : Fin k, ((m j i).natAbs : ℝ) / ((Nord i : ℝ) + 1)
        = (∑ i : Fin k, ((m j i).natAbs : ℝ)) / ((Nmax : ℝ) + 1) := by
      rw [Finset.sum_div]
    have hcast : (∑ i : Fin k, ((m j i).natAbs : ℝ)) = ((∑ i : Fin k, (m j i).natAbs : ℕ) : ℝ) :=
      (Nat.cast_sum Finset.univ fun i => (m j i).natAbs).symm
    have hnum : (∑ i : Fin k, ((m j i).natAbs : ℝ)) ≤ (M : ℝ) := by
      rw [hcast]
      exact_mod_cast hrow j
    rw [hsum]
    exact (div_le_div_iff_of_pos_right hX).mpr hnum
  have hsmall : A * ((M : ℝ) / ((Nmax : ℝ) + 1)) ≤ δ / 3 := by
    have hN0' : 3 * A * (M : ℝ) / δ < (N0 : ℝ) := hN0
    have hNle : (N0 : ℝ) ≤ (Nmax : ℝ) := by
      have : N0 ≤ Nmax := le_max_right _ _
      exact_mod_cast this
    have hstep : 3 * A * (M : ℝ) < δ * ((Nmax : ℝ) + 1) := by
      rw [div_lt_iff₀ hδ] at hN0'
      nlinarith [hN0', hNle, hδ]
    rw [mul_div_assoc'] at *
    rw [div_le_div_iff₀ hX (by norm_num : (0:ℝ) < 3)]
    nlinarith [hstep]
  -- the operator output is a spectral polynomial
  obtain ⟨S, a, hSspec, hSeq⟩ := exists_spectrum_trigPoly_of_coeff_sum
    (Fintype.piFinset fun j : Fin k => Finset.range (Nord j + 1) ×ˢ Finset.range (Nord j + 1))
    (fun _ : Fin k → ℕ × ℕ => ∏ j : Fin k, ((Nord j : ℂ) + 1)⁻¹)
    (fun v : Fin k → ℕ × ℕ => -(∑ j : Fin k, (((v j).1 : ℝ) - ((v j).2 : ℝ)) * β j))
    (fun x => f x)
  refine ⟨S, a, hSspec, fun t => ?_⟩
  have hTf : bohrMean (fun u => f (u + t) * multiFejerKernel β Nord u)
      = ∑ lam ∈ S, a lam * expChar lam t := by
    rw [bohrMean_translate_mul_multiFejerKernel β Nord hfc hfa t]
    exact hSeq t
  rw [← hTf]
  -- the three errors
  have hKc : Continuous (multiFejerKernel β Nord) := continuous_multiFejerKernel β Nord
  have hKa : HTGeometry.IsBohrAlmostPeriodic (multiFejerKernel β Nord) :=
    isBohrAlmostPeriodic_multiFejerKernel β Nord
  have hPKc : Continuous fun u : ℝ => P (u + t) * multiFejerKernel β Nord u :=
    (hPc.comp (continuous_id.add continuous_const)).mul hKc
  have hPKa : HTGeometry.IsBohrAlmostPeriodic fun u : ℝ =>
      P (u + t) * multiFejerKernel β Nord u :=
    isBohrAlmostPeriodic_mul (hPc.comp (continuous_id.add continuous_const))
      (isBohrAlmostPeriodic_comp_add_const hPa t) hKc hKa
  have hfKc : Continuous fun u : ℝ => f (u + t) * multiFejerKernel β Nord u :=
    (hfc.comp (continuous_id.add continuous_const)).mul hKc
  have hfKa : HTGeometry.IsBohrAlmostPeriodic fun u : ℝ =>
      f (u + t) * multiFejerKernel β Nord u :=
    isBohrAlmostPeriodic_mul (hfc.comp (continuous_id.add continuous_const))
      (isBohrAlmostPeriodic_comp_add_const hfa t) hKc hKa
  have hlin : bohrMean (fun u => P (u + t) * multiFejerKernel β Nord u)
      - bohrMean (fun u => f (u + t) * multiFejerKernel β Nord u)
      = bohrMean (fun u => (P (u + t) - f (u + t)) * multiFejerKernel β Nord u) := by
    rw [← bohrMean_sub hPKc hPKa hfKc hfKa]
    congr 1
    funext u
    ring
  have hsplit : (f t : ℂ) - bohrMean (fun u => f (u + t) * multiFejerKernel β Nord u)
      = (f t - P t) + (P t - bohrMean (fun u => P (u + t) * multiFejerKernel β Nord u))
        + bohrMean (fun u => (P (u + t) - f (u + t)) * multiFejerKernel β Nord u) := by
    rw [← hlin]
    ring
  rw [hsplit]
  refine le_trans (norm_add₃_le) ?_
  -- the middle error: the multipliers
  have hmid : ‖P t - bohrMean (fun u => P (u + t) * multiFejerKernel β Nord u)‖ ≤ δ / 3 := by
    have hact := bohrMean_translate_trigPoly_mul_multiFejerKernel hind Nord c m hmN t
    have hPt : P t = ∑ j : Fin n, c j * expChar (∑ i : Fin k, (m j i : ℝ) * β i) t := rfl
    rw [hPt, hact, ← Finset.sum_sub_distrib]
    have hterm : ∀ j : Fin n,
        ‖c j * expChar (∑ i : Fin k, (m j i : ℝ) * β i) t
          - c j * ((fejerMultiplier Nord (m j) : ℝ) : ℂ)
            * expChar (∑ i : Fin k, (m j i : ℝ) * β i) t‖
          ≤ ‖c j‖ * ((M : ℝ) / ((Nmax : ℝ) + 1)) := by
      intro j
      have hfac : c j * expChar (∑ i : Fin k, (m j i : ℝ) * β i) t
          - c j * ((fejerMultiplier Nord (m j) : ℝ) : ℂ)
            * expChar (∑ i : Fin k, (m j i : ℝ) * β i) t
          = (c j * ((1 - fejerMultiplier Nord (m j) : ℝ) : ℂ))
            * expChar (∑ i : Fin k, (m j i : ℝ) * β i) t := by
        push_cast
        ring
      rw [hfac, norm_mul, norm_expChar, mul_one, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hnn : 0 ≤ 1 - fejerMultiplier Nord (m j) := by
        have := fejerMultiplier_le_one Nord (m j) (fun i => hmN j i)
        linarith
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hdefect j
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun j _ => hterm j) ?_
    rw [← Finset.sum_mul]
    exact hsmall
  -- the outer errors
  have hout : ‖bohrMean (fun u => (P (u + t) - f (u + t)) * multiFejerKernel β Nord u)‖
      ≤ δ / 3 := by
    have hgc : Continuous fun x : ℝ => P x - f x := hPc.sub hfc
    have hga : HTGeometry.IsBohrAlmostPeriodic fun x : ℝ => P x - f x :=
      isBohrAlmostPeriodic_sub hPc hPa hfc hfa
    have hB : ∀ x : ℝ, ‖P x - f x‖ ≤ δ / 3 := by
      intro x
      rw [norm_sub_rev]
      exact hPclose x
    exact norm_bohrMean_translate_mul_multiFejerKernel_le hind Nord hgc hga hB t
  have h1 := hPclose t
  linarith [h1, hmid, hout]

end

end GaloisForLFunctions
