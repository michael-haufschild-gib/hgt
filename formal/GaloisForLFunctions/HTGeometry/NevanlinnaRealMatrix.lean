import GaloisForLFunctions.HTGeometry.NevDSeriesNonzero
import GaloisForLFunctions.HTGeometry.NevanlinnaClassicalInterface

/-!
# The limiting Nevanlinna matrix on the real axis

The four entries have real coefficients, so at a real point each is the complex embedding of a real
series.  Transporting the determinant identity along that embedding gives a
`ClassicalNevanlinnaMatrixData ℝ`, and continuity of the real entries follows from entirety of the
complex ones by composing with `Complex.ofReal` and taking real parts.

This is the limit of the truncated matrix of `NevanlinnaPluecker`: the finite sums there become the
kernel series here, and it is the limit whose denominator fibers are the N-extremal supports.
-/

open scoped BigOperators

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- Complex evaluation of the second-kind polynomial at a real point is the real evaluation. -/
theorem secondKindC_ofReal (s : ℕ → ℝ) (k : ℕ) (x : ℝ) :
    secondKindC s k (x : ℂ) = ((((secondKind s k).eval x) : ℝ) : ℂ) := by
  rw [secondKindC]
  simpa using Polynomial.aeval_algebraMap_apply ℂ x (secondKind s k)

theorem secondKindC_at_zero (s : ℕ → ℝ) (k : ℕ) :
    secondKindC s k (0 : ℂ) = ((((secondKind s k).eval (0:ℝ)) : ℝ) : ℂ) := by
  simpa using secondKindC_ofReal s k 0

theorem monicOrthoC_at_zero (s : ℕ → ℝ) (k : ℕ) :
    monicOrthoC s k (0 : ℂ) = ((((monicOrtho s k).eval (0:ℝ)) : ℝ) : ℂ) := by
  simpa using monicOrthoC_ofReal s k 0

/-- The complex embedding of a real bilinear kernel series. -/
theorem ofReal_bilinear_tsum (s : ℕ → ℝ) (f g : ℕ → ℝ) :
    ((∑' k, f k * g k / momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)
      = ∑' k, ((f k : ℝ) : ℂ) * ((g k : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun k => ?_
  push_cast
  ring

/-- The `A` entry on the real axis. -/
noncomputable def nevArealInf (s : ℕ → ℝ) (x : ℝ) : ℝ :=
  momentInner s (monicOrtho s 0) (monicOrtho s 0) * x *
    ∑' k, (secondKind s k).eval 0 * (secondKind s k).eval x /
      momentInner s (monicOrtho s k) (monicOrtho s k)

/-- The `B` entry on the real axis. -/
noncomputable def nevBrealInf (s : ℕ → ℝ) (x : ℝ) : ℝ :=
  -1 + momentInner s (monicOrtho s 0) (monicOrtho s 0) * x *
    ∑' k, (monicOrtho s k).eval x * (secondKind s k).eval 0 /
      momentInner s (monicOrtho s k) (monicOrtho s k)

/-- The `C` entry on the real axis. -/
noncomputable def nevCrealInf (s : ℕ → ℝ) (x : ℝ) : ℝ :=
  1 + momentInner s (monicOrtho s 0) (monicOrtho s 0) * x *
    ∑' k, (monicOrtho s k).eval 0 * (secondKind s k).eval x /
      momentInner s (monicOrtho s k) (monicOrtho s k)

/-- The `D` entry on the real axis. -/
noncomputable def nevDrealInf (s : ℕ → ℝ) (x : ℝ) : ℝ :=
  momentInner s (monicOrtho s 0) (monicOrtho s 0) * x *
    ∑' k, (monicOrtho s k).eval 0 * (monicOrtho s k).eval x /
      momentInner s (monicOrtho s k) (monicOrtho s k)

theorem nevAinf_ofReal (s : ℕ → ℝ) (x : ℝ) :
    nevAinf s ((x : ℝ) : ℂ) = ((nevArealInf s x : ℝ) : ℂ) := by
  have htsum : ∑' k, secondKindC s k 0 * secondKindC s k ((x : ℝ) : ℂ) /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)
      = ((∑' k, (secondKind s k).eval 0 * (secondKind s k).eval x /
          momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := by
    rw [ofReal_bilinear_tsum]
    exact tsum_congr fun k => by rw [secondKindC_at_zero, secondKindC_ofReal]
  simp only [nevAinf, nevArealInf, htsum, Complex.ofReal_mul]

theorem nevBinf_ofReal (s : ℕ → ℝ) (x : ℝ) :
    nevBinf s ((x : ℝ) : ℂ) = ((nevBrealInf s x : ℝ) : ℂ) := by
  have htsum : ∑' k, monicOrthoC s k ((x : ℝ) : ℂ) * secondKindC s k 0 /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)
      = ((∑' k, (monicOrtho s k).eval x * (secondKind s k).eval 0 /
          momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := by
    rw [ofReal_bilinear_tsum]
    exact tsum_congr fun k => by rw [monicOrthoC_ofReal, secondKindC_at_zero]
  simp only [nevBinf, nevBrealInf, htsum, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_one]

theorem nevCinf_ofReal (s : ℕ → ℝ) (x : ℝ) :
    nevCinf s ((x : ℝ) : ℂ) = ((nevCrealInf s x : ℝ) : ℂ) := by
  have htsum : ∑' k, monicOrthoC s k 0 * secondKindC s k ((x : ℝ) : ℂ) /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)
      = ((∑' k, (monicOrtho s k).eval 0 * (secondKind s k).eval x /
          momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := by
    rw [ofReal_bilinear_tsum]
    exact tsum_congr fun k => by rw [monicOrthoC_at_zero, secondKindC_ofReal]
  simp only [nevCinf, nevCrealInf, htsum, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_one]

theorem nevDinf_ofReal (s : ℕ → ℝ) (x : ℝ) :
    nevDinf s ((x : ℝ) : ℂ) = ((nevDrealInf s x : ℝ) : ℂ) := by
  have htsum : ∑' k, monicOrthoC s k 0 * monicOrthoC s k ((x : ℝ) : ℂ) /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)
      = ((∑' k, (monicOrtho s k).eval 0 * (monicOrtho s k).eval x /
          momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := by
    rw [ofReal_bilinear_tsum]
    exact tsum_congr fun k => by rw [monicOrthoC_at_zero, monicOrthoC_ofReal]
  simp only [nevDinf, nevDrealInf, htsum, Complex.ofReal_mul]

/-- **The determinant identity on the real axis.** -/
theorem nev_realInf_det_one (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (x : ℝ) :
    nevArealInf s x * nevDrealInf s x - nevBrealInf s x * nevCrealInf s x = 1 := by
  obtain ⟨-, -, -, -, hdet⟩ := nevanlinna_entire_unimodular h h0b
  have hx := hdet ((x : ℝ) : ℂ)
  rw [nevAinf_ofReal, nevBinf_ofReal, nevCinf_ofReal, nevDinf_ofReal] at hx
  exact_mod_cast hx

/-- Each real entry is the real part of the entire one along the embedding, hence continuous. -/
theorem continuous_of_entire_ofReal {f : ℂ → ℂ} {g : ℝ → ℝ} (hf : Differentiable ℂ f)
    (hfg : ∀ x : ℝ, f ((x : ℝ) : ℂ) = ((g x : ℝ) : ℂ)) : Continuous g := by
  have hc : Continuous fun x : ℝ => f ((x : ℝ) : ℂ) :=
    hf.continuous.comp Complex.continuous_ofReal
  have hre : g = fun x : ℝ => (f ((x : ℝ) : ℂ)).re := by
    funext x
    rw [hfg x, Complex.ofReal_re]
  rw [hre]
  exact Complex.continuous_re.comp hc

theorem continuous_nevBrealInf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    Continuous (nevBrealInf s) := by
  obtain ⟨-, hB, -, -, -⟩ := nevanlinna_entire_unimodular h h0b
  exact continuous_of_entire_ofReal hB (nevBinf_ofReal s)

theorem continuous_nevDrealInf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    Continuous (nevDrealInf s) := by
  obtain ⟨-, -, -, hD, -⟩ := nevanlinna_entire_unimodular h h0b
  exact continuous_of_entire_ofReal hD (nevDinf_ofReal s)

theorem continuous_nevArealInf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    Continuous (nevArealInf s) := by
  obtain ⟨hA, -, -, -, -⟩ := nevanlinna_entire_unimodular h h0b
  exact continuous_of_entire_ofReal hA (nevAinf_ofReal s)

theorem continuous_nevCrealInf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    Continuous (nevCrealInf s) := by
  obtain ⟨-, -, hC, -, -⟩ := nevanlinna_entire_unimodular h h0b
  exact continuous_of_entire_ofReal hC (nevCinf_ofReal s)

/-- **The classical Nevanlinna matrix of an indeterminate moment problem.**  This is the `matrix`
field of `ClassicalNevanlinnaExtremalFamily`, built rather than assumed. -/
noncomputable def nevMatrixDataInf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaMatrixData ℝ where
  A := nevArealInf s
  B := nevBrealInf s
  C := nevCrealInf s
  D := nevDrealInf s
  det_one := nev_realInf_det_one h h0b

@[simp] theorem nevMatrixData_B (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    (nevMatrixDataInf h h0b).B = nevBrealInf s := rfl

@[simp] theorem nevMatrixData_D (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    (nevMatrixDataInf h h0b).D = nevDrealInf s := rfl

/-- The continuity fields of `ClassicalNevanlinnaExtremalFamily` for the limiting matrix. -/
theorem continuous_nevMatrixDataInf_B (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    Continuous (nevMatrixDataInf h h0b).B :=
  continuous_nevBrealInf h h0b

theorem continuous_nevMatrixDataInf_D (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    Continuous (nevMatrixDataInf h h0b).D :=
  continuous_nevDrealInf h h0b

/-- The real embedding is a filter map of punctured neighbourhoods. -/
theorem tendsto_ofReal_nhdsWithin_ne (x : ℝ) :
    Filter.Tendsto (fun y : ℝ => (y : ℂ)) (nhdsWithin x {x}ᶜ)
      (nhdsWithin ((x : ℝ) : ℂ) {((x : ℝ) : ℂ)}ᶜ) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨Complex.continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
  exact fun hc => hy (Complex.ofReal_inj.mp hc)

/-- The finite denominator fiber is the real trace of the complex zero set of `B τ − D`. -/
theorem nevMatrixDataInf_finiteDenominatorFiber_eq (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (tau : ℝ) :
    (nevMatrixDataInf h h0b).finiteDenominatorFiber tau
      = {x : ℝ | nevBinf s ((x : ℝ) : ℂ) * ((tau : ℝ) : ℂ) - nevDinf s ((x : ℝ) : ℂ) = 0} := by
  ext x
  simp only [GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaMatrixData.finiteDenominatorFiber,
    Set.mem_setOf_eq, nevMatrixDataInf]
  rw [nevBinf_ofReal, nevDinf_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.ofReal_eq_zero]

/-- The infinity denominator fiber is the real trace of the complex zero set of `B`. -/
theorem nevMatrixDataInf_infinityDenominatorFiber_eq (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) :
    (nevMatrixDataInf h h0b).infinityDenominatorFiber
      = {x : ℝ | nevBinf s ((x : ℝ) : ℂ) = 0} := by
  ext x
  simp only [GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaMatrixData.infinityDenominatorFiber,
    Set.mem_setOf_eq, nevMatrixDataInf]
  rw [nevBinf_ofReal, Complex.ofReal_eq_zero]

/-- **Every finite denominator fiber is discrete.**  This is the N-extremal support of the parameter
`τ`: around each of its points there is a punctured neighbourhood meeting it nowhere. -/
theorem eventually_notMem_finiteDenominatorFiber (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (tau : ℝ) (x : ℝ) :
    ∀ᶠ y in nhdsWithin x {x}ᶜ, y ∉ (nevMatrixDataInf h h0b).finiteDenominatorFiber tau := by
  have hc := eventually_ne_zero_nevCombination_all h h0b ((tau : ℝ) : ℂ) ((x : ℝ) : ℂ)
  filter_upwards [(tendsto_ofReal_nhdsWithin_ne x).eventually hc] with y hy
  rw [nevMatrixDataInf_finiteDenominatorFiber_eq]
  exact hy

/-- **The infinity denominator fiber is discrete.** -/
theorem eventually_notMem_infinityDenominatorFiber (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (x : ℝ) :
    ∀ᶠ y in nhdsWithin x {x}ᶜ, y ∉ (nevMatrixDataInf h h0b).infinityDenominatorFiber := by
  have hc := eventually_ne_zero_nevBinf h h0b ((x : ℝ) : ℂ)
  filter_upwards [(tendsto_ofReal_nhdsWithin_ne x).eventually hc] with y hy
  rw [nevMatrixDataInf_infinityDenominatorFiber_eq]
  exact hy

end HTGeometry
