import GaloisForLFunctions.RHTower.Suzuki.SuzukiCarlemanFlatPortResponse

/-!
# The scalar seam integral of the paired Carleman port

The opposite-side contribution at a seam carries the exact scalar factor

`∫_0^∞ dv / (1 + e^{v-L}) = L + log (1 + e^{-L})`,

whose primitive is `v - log (1 + e^{v-L})`.  The exponentially small correction `q(L)` is the
entire deviation from the bare `L`, which is why the paired normal form has `2L + q(L)` on its
diagonal.
-/

open Set MeasureTheory Filter Topology

namespace RHTower

noncomputable section

/-- The primitive of the Carleman cutoff factor in the cutoff scale. -/
def carlemanScalarPrimitive (L v : ℝ) : ℝ := v - Real.log (1 + Real.exp (v - L))

theorem hasDerivAt_carlemanScalarPrimitive (L v : ℝ) :
    HasDerivAt (carlemanScalarPrimitive L) (carlemanCutoffFactor L v) v := by
  have hpos : (0:ℝ) < 1 + Real.exp (v - L) := by
    have := Real.exp_pos (v - L)
    linarith
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (x - L)) (Real.exp (v - L)) v := by
    have h1 : HasDerivAt (fun x : ℝ => x - L) 1 v := by
      simpa using (hasDerivAt_id v).sub_const L
    simpa using h1.exp
  have hbase : HasDerivAt (fun x : ℝ => 1 + Real.exp (x - L)) (Real.exp (v - L)) v := by
    simpa using hexp.const_add (1:ℝ)
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + Real.exp (x - L)))
      (Real.exp (v - L) / (1 + Real.exp (v - L))) v := hbase.log (ne_of_gt hpos)
  have hid : HasDerivAt (fun x : ℝ => x) 1 v := hasDerivAt_id' v
  have hsub : HasDerivAt (fun x : ℝ => x - Real.log (1 + Real.exp (x - L)))
      (1 - Real.exp (v - L) / (1 + Real.exp (v - L))) v := hid.sub hlog
  have hval : (1 : ℝ) - Real.exp (v - L) / (1 + Real.exp (v - L)) = carlemanCutoffFactor L v := by
    rw [carlemanCutoffFactor]
    field_simp
    ring
  have hfun : carlemanScalarPrimitive L
      = fun x : ℝ => x - Real.log (1 + Real.exp (x - L)) := by
    funext x
    rw [carlemanScalarPrimitive]
  rw [hfun, ← hval]
  exact hsub

theorem tendsto_carlemanScalarPrimitive (L : ℝ) :
    Tendsto (carlemanScalarPrimitive L) atTop (𝓝 L) := by
  have hsplit : ∀ v : ℝ, carlemanScalarPrimitive L v = L - Real.log (1 + Real.exp (L - v)) := by
    intro v
    have hpos : (0:ℝ) < Real.exp (v - L) := Real.exp_pos _
    have hfac : 1 + Real.exp (v - L) = Real.exp (v - L) * (1 + Real.exp (L - v)) := by
      rw [mul_add, mul_one, ← Real.exp_add]
      have : v - L + (L - v) = 0 := by ring
      rw [this, Real.exp_zero]
      ring
    rw [carlemanScalarPrimitive, hfac, Real.log_mul (ne_of_gt hpos) (by
      have := Real.exp_pos (L - v)
      linarith), Real.log_exp]
    ring
  have hlim : Tendsto (fun v : ℝ => L - Real.log (1 + Real.exp (L - v))) atTop (𝓝 (L - 0)) := by
    apply Filter.Tendsto.const_sub
    have hexp : Tendsto (fun v : ℝ => Real.exp (L - v)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun v : ℝ => L - v) atTop atBot :=
        tendsto_atBot_add_const_left _ L tendsto_neg_atTop_atBot
      exact Real.tendsto_exp_atBot.comp h1
    have h2 : Tendsto (fun v : ℝ => Real.log (1 + Real.exp (L - v))) atTop
        (𝓝 (Real.log (1 + 0))) := by
      apply Filter.Tendsto.log _ (by norm_num)
      exact tendsto_const_nhds.add hexp
    simpa using h2
  rw [sub_zero] at hlim
  exact hlim.congr fun v => (hsplit v).symm

/-- **`(13)`: the exact scalar seam integral.** -/
theorem integral_Ioi_carlemanCutoffFactor (L : ℝ) :
    (∫ v in Ioi (0:ℝ), carlemanCutoffFactor L v) = L + Real.log (1 + Real.exp (-L)) := by
  have hderiv : ∀ v ∈ Ioi (0:ℝ),
      HasDerivAt (carlemanScalarPrimitive L) (carlemanCutoffFactor L v) v :=
    fun v _ => hasDerivAt_carlemanScalarPrimitive L v
  have hnn : ∀ v ∈ Ioi (0:ℝ), 0 ≤ carlemanCutoffFactor L v :=
    fun v _ => (carlemanCutoffFactor_pos L v).le
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    (hasDerivAt_carlemanScalarPrimitive L 0).continuousAt.continuousWithinAt hderiv hnn
    (tendsto_carlemanScalarPrimitive L)
  rw [h, carlemanScalarPrimitive]
  have : (0:ℝ) - L = -L := by ring
  rw [this]
  ring

end

end RHTower
