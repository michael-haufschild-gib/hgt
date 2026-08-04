import GaloisForLFunctions.RHTower.Sieve.InvZetaRegular

/-!
# A zero-free rectangle at every height

The quantitative zero-free region proved in `ZeroFreeAssembly` covers heights `|γ| ≥ 1`.  Near the
real axis it says nothing, and there the argument is different in kind: `ζ` is nonvanishing on the
whole closed segment `{1 + it : |t| ≤ T}` — off the pole because `re s = 1`, and at `s = 1` itself
because `ζ` has a pole there, so the entire unit `G = (s-1)ζ` takes the value `1`.  That segment is
compact and the nonvanishing locus of `G` is open, so a whole thickening of the segment is
zero-free.

Combining the two gives, for every height `T`, an honest rectangle `[c, d] × [-T, T]` with `c < 1`
on which `ζ` has no zeros — hence on which `invZeta` is holomorphic.  This is the hypothesis
`integral_invZeta_vertical_sub_eq_horizontal_rect` consumes, and it is now supplied
unconditionally rather than assumed.
-/

namespace RHTower.Sieve

open Complex RHTower Metric

/-- The entire unit `G = (s-1)·ζ(s)` is nonvanishing on the abscissa `re s = 1`.  Off the pole this
is the nonvanishing of `ζ` there; at the pole it is `G(1) = 1`. -/
theorem zetaResidueUnit_ne_zero_on_one_line (t : ℝ) :
    zetaResidueUnit ((1 : ℂ) + (t : ℝ) * Complex.I) ≠ 0 := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · have hne : ((1 : ℂ) + (t : ℝ) * Complex.I) ≠ 1 := by
      intro h
      exact ht (by simpa using congrArg Complex.im h)
    have hre : ((1 : ℂ) + (t : ℝ) * Complex.I).re = 1 := by simp
    have hz : riemannZeta ((1 : ℂ) + (t : ℝ) * Complex.I) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by rw [hre])
    exact (zetaResidueUnit_ne_zero_iff hne).2 hz

/-- `zetaResidueUnit` is continuous, being entire. -/
theorem continuous_zetaResidueUnit : Continuous zetaResidueUnit :=
  continuous_iff_continuousAt.2 fun s => (analyticAt_zetaResidueUnit s).continuousAt

/-- **A zero-free box up to any fixed height.**  For every `T` there is `δ > 0` such that `ζ` has no
zero `s` with `1 - δ ≤ re s ≤ 1` and `|im s| ≤ T`.  The proof thickens the compact segment
`{1 + it : |t| ≤ T}`, on which the entire unit `G` is nonvanishing, inside the open set `{G ≠ 0}`. -/
theorem exists_zero_free_box (T : ℝ) :
    ∃ δ > 0, ∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ 1 → |s.im| ≤ T → s ≠ 1 → riemannZeta s ≠ 0 := by
  set S : Set ℂ := (fun t : ℝ => (1 : ℂ) + (t : ℝ) * Complex.I) '' Set.Icc (-T) T with hSdef
  have hS : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hU : IsOpen {s : ℂ | zetaResidueUnit s ≠ 0} :=
    isOpen_compl_singleton.preimage continuous_zetaResidueUnit
  have hSU : S ⊆ {s : ℂ | zetaResidueUnit s ≠ 0} := by
    rintro s ⟨t, -, rfl⟩
    exact zetaResidueUnit_ne_zero_on_one_line t
  obtain ⟨δ, hδ, hsub⟩ := hS.exists_thickening_subset_open hU hSU
  refine ⟨δ / 2, by linarith, fun s hlo hhi him hs1 => ?_⟩
  have hmem : ((1 : ℂ) + (s.im : ℝ) * Complex.I) ∈ S := by
    exact ⟨s.im, (abs_le.1 him), rfl⟩
  have hdiff : s - ((1 : ℂ) + (s.im : ℝ) * Complex.I) = ((s.re - 1 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hdist : dist s ((1 : ℂ) + (s.im : ℝ) * Complex.I) < δ := by
    rw [Complex.dist_eq, hdiff, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hin : s ∈ thickening δ S := Metric.mem_thickening_iff.2 ⟨_, hmem, hdist⟩
  exact (zetaResidueUnit_ne_zero_iff hs1).1 (hsub hin)

/-- **A zero-free rectangle at every height.**  Combining the box near the real axis with the
nonvanishing of `ζ` on `re s ≥ 1`, every rectangle `[c, d] × [-T, T]` with `1 - δ ≤ c ≤ 1 ≤ d` is
free of zeros of `ζ`. -/
theorem exists_zero_free_rect {T : ℝ} (hT : 0 ≤ T) :
    ∃ δ > 0, ∀ c d : ℝ, 1 - δ ≤ c → c ≤ 1 → 1 ≤ d →
      ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0 := by
  obtain ⟨δ, hδ, hbox⟩ := exists_zero_free_box T
  refine ⟨δ, hδ, fun c d hc hc1 hd s hs hs1 => ?_⟩
  rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hs
  obtain ⟨⟨hre1, -⟩, hima, himb⟩ := hs
  rcases le_or_gt s.re 1 with hle | hgt
  · exact hbox s (by linarith) hle (abs_le.2 ⟨hima, himb⟩) hs1
  · exact riemannZeta_ne_zero_of_one_le_re hgt.le

/-- **`invZeta` is holomorphic on a zero-free rectangle at every height.**  Unconditional: for each
`T` there is a genuine `δ > 0` and every rectangle `[c, d] × [-T, T]` with `1 - δ ≤ c ≤ 1 ≤ d`
carries a holomorphic branch of `1/ζ`, the pole of `ζ` inside it costing nothing. -/
theorem exists_differentiableOn_invZeta_rect {T : ℝ} (hT : 0 ≤ T) :
    ∃ δ > 0, ∀ c d : ℝ, 1 - δ ≤ c → c ≤ 1 → 1 ≤ d →
      DifferentiableOn ℂ invZeta (Set.uIcc c d ×ℂ Set.uIcc (-T) T) := by
  obtain ⟨δ, hδ, hzf⟩ := exists_zero_free_rect hT
  exact ⟨δ, hδ, fun c d hc hc1 hd => differentiableOn_invZeta_rect (hzf c d hc hc1 hd)⟩

/-- **The truncated contour shift for `1/ζ`, unconditionally.**  At every height `T` the shift
identity holds for `invZeta` across some rectangle crossing the abscissa `re s = 1`. -/
theorem exists_integral_invZeta_shift {T : ℝ} (hT : 0 ≤ T) :
    ∃ δ > 0, ∀ c d : ℝ, 1 - δ ≤ c → c ≤ 1 → 1 ≤ d →
      (Complex.I • (∫ y : ℝ in (-T)..T, invZeta ((d : ℂ) + (y : ℝ) * Complex.I)))
          - Complex.I • (∫ y : ℝ in (-T)..T, invZeta ((c : ℂ) + (y : ℝ) * Complex.I))
        = (∫ x : ℝ in c..d, invZeta ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
          - ∫ x : ℝ in c..d, invZeta ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) := by
  obtain ⟨δ, hδ, hzf⟩ := exists_zero_free_rect hT
  exact ⟨δ, hδ, fun c d hc hc1 hd =>
    integral_invZeta_vertical_sub_eq_horizontal_rect (hzf c d hc hc1 hd)⟩

end RHTower.Sieve
