import GaloisForLFunctions.PNTPlus.ResidueCalcOnRectangles

/-!
# The residue of the truncated Perron kernel

`y^s/s` has a simple pole at the origin with residue `1`: its principal part there is exactly `1/s`,
because `(y^s - 1)/s` tends to `log y`.  So the rectangle residue theorem gives

`RectangleIntegral' (fun s => y^s/s) z w = 1`

for every rectangle whose interior contains `0`.  Together with the three segment estimates of
`HTGeometry/PerronKernelSegments` this is Perron's lemma: the rectangle integral is the difference of the
two vertical edges plus the two horizontal ones, the edge at `Re s = -A` vanishes as `A → ∞`, and the
horizontal pieces are `O(y^σ/(T log y))`.

The residue theorem itself is PNTPlus's `ResidueTheoremOnRectangleWithSimplePole'`; only the principal
part of this particular kernel is proved here.
-/

noncomputable section
namespace RHTower.Sieve
open Complex Topology Filter Asymptotics

/-- **The residue of the Perron kernel.**  `y^s/s` has a simple pole at `s = 0` with residue `1`, so
every rectangle whose interior contains the origin integrates it to `1`. -/
theorem rectangleIntegral'_cpow_div_eq_one {y : ℝ} (hy : 0 < y) {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) (h0 : Rectangle z w ∈ 𝓝 (0 : ℂ)) :
    RectangleIntegral' (fun s : ℂ => (y : ℂ) ^ s / s) z w = 1 := by
  have hy0 : ((y : ℂ)) ≠ 0 := by
    simpa using hy.ne'
  refine ResidueTheoremOnRectangleWithSimplePole' (A := 1) hre him h0 ?_ ?_
  · intro s hs
    have hsne : s ≠ 0 := fun h => hs.2 (by simp [h])
    refine DifferentiableWithinAt.div ?_ differentiableWithinAt_id hsne
    exact (differentiableAt_id.const_cpow (Or.inl hy0)).differentiableWithinAt
  · have hderiv : HasDerivAt (fun s : ℂ => (y : ℂ) ^ s) ((y : ℂ) ^ (0 : ℂ) * Complex.log y) 0 :=
      (hasStrictDerivAt_const_cpow (Or.inl hy0)).hasDerivAt
    have hslope := hasDerivAt_iff_tendsto_slope.mp hderiv
    have hbig := hslope.isBigO_one ℂ
    refine hbig.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsne : s ≠ 0 := hs
    rw [slope_def_field]
    simp only [Pi.sub_apply, sub_zero, Complex.cpow_zero]
    field_simp

end RHTower.Sieve
end
