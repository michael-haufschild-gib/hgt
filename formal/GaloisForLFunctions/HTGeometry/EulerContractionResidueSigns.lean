import GaloisForLFunctions.HTGeometry.LogarithmicResidueQuantization

/-!
# Paired residues of an Euler-contracted logarithmic connection

The Euler contraction `ι_{z∂z}(-d log f) = -z (log f)'(z)` of the logarithmic connection form of
an even function is again even, so every divisor point `a` is matched by a divisor point `-a` of
the same order.  At a point of order `n` the contraction has residue `-n a`, hence residue `+n a`
at the reflected point.  For a real `a > 0` and a genuine zero these two residues are real with
opposite signs, so no fixed orientation of the residue sign can hold at both: the contracted
scalar is neither a Herglotz nor an anti-Herglotz carrier.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

/-- Euler contraction of the logarithmic connection one-form. -/
noncomputable def eulerContraction (f : ℂ → ℂ) (z : ℂ) : ℂ := -z * logDeriv f z

/-- An even function has an odd derivative. -/
theorem deriv_neg_of_even {f : ℂ → ℂ} (hf : ∀ z, f (-z) = f z) (z : ℂ) :
    deriv f (-z) = -deriv f z := by
  have hfun : (fun w : ℂ => f (-w)) = f := funext hf
  have h := deriv_comp_neg (f := f) (x := z)
  rw [hfun] at h
  linear_combination h

/-- An even function has an odd logarithmic derivative. -/
theorem logDeriv_neg_of_even {f : ℂ → ℂ} (hf : ∀ z, f (-z) = f z) (z : ℂ) :
    logDeriv f (-z) = -logDeriv f z := by
  rw [logDeriv_apply, logDeriv_apply, deriv_neg_of_even hf, hf]
  ring

/-- The Euler contraction of an even function is even. -/
theorem eulerContraction_even {f : ℂ → ℂ} (hf : ∀ z, f (-z) = f z) (z : ℂ) :
    eulerContraction f (-z) = eulerContraction f z := by
  rw [eulerContraction, eulerContraction, logDeriv_neg_of_even hf]
  ring

/-- Residue of the Euler contraction at a divisor point of order `n`. -/
theorem tendsto_eulerContraction_residue {f : ℂ → ℂ} {a : ℂ} {n : ℤ}
    (hf : MeromorphicAt f a) (horder : meromorphicOrderAt f a = n) :
    Tendsto (fun z => (z - a) * eulerContraction f z) (𝓝[≠] a) (𝓝 (-(n : ℂ) * a)) := by
  have h := logDeriv_residue_of_meromorphicOrder hf horder
  have hneg : Tendsto (fun z : ℂ => -z) (𝓝[≠] a) (𝓝 (-a)) :=
    (continuous_neg.tendsto a).mono_left nhdsWithin_le_nhds
  have hmul := hneg.mul h
  have hval : (-a) * (n : ℂ) = -(n : ℂ) * a := by ring
  rw [hval] at hmul
  refine Tendsto.congr (fun z => ?_) hmul
  simp only [eulerContraction]
  ring

/-- The reflected divisor point carries the opposite residue. -/
theorem tendsto_eulerContraction_residue_reflected {f : ℂ → ℂ} {a : ℂ} {n : ℤ}
    (hf : MeromorphicAt f a) (horder : meromorphicOrderAt f a = n)
    (heven : ∀ z, f (-z) = f z) :
    Tendsto (fun z => (z + a) * eulerContraction f z) (𝓝[≠] (-a)) (𝓝 ((n : ℂ) * a)) := by
  have hmap : Tendsto (fun z : ℂ => -z) (𝓝[≠] (-a)) (𝓝[≠] a) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h := (continuous_neg.tendsto (-a)).mono_left
        (nhdsWithin_le_nhds (s := ({-a}ᶜ : Set ℂ)))
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z ≠ -a := hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcontra
      exact hz' (by linear_combination -hcontra)
  have h := ((tendsto_eulerContraction_residue hf horder).comp hmap).neg
  have hval : -(-(n : ℂ) * a) = (n : ℂ) * a := by ring
  rw [hval] at h
  refine Tendsto.congr (fun z => ?_) h
  simp only [Function.comp_apply]
  rw [eulerContraction_even heven]
  ring

/-- **No uniform residue orientation.**  At a real divisor point `a > 0` of positive order the two
paired residues of the Euler contraction are real with strictly opposite signs, so neither the
Herglotz nor the anti-Herglotz sign convention can hold at both. -/
theorem not_exists_uniform_eulerContraction_residue_sign {a : ℝ} (ha : 0 < a) {n : ℤ}
    (hn : 1 ≤ n) :
    ¬ ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ 0 < ε * (-(n : ℝ) * a) ∧ 0 < ε * ((n : ℝ) * a) := by
  rintro ⟨ε, hε, h1, h2⟩
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hna : 0 < (n : ℝ) * a := mul_pos (by linarith) ha
  rcases hε with rfl | rfl <;> nlinarith

end GaloisForLFunctions.HTGeometry
