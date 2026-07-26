import GaloisForLFunctions.RHTower.ComplementaryPacketKernelIntegrability

/-!
# Affine flux of the complementary packet

Extending the boundary packet kernel to the whole line by its incoming constant,

```text
b_ω(t) = k_ω(t)   (t ≥ 0),      b_ω(t) = -c_ω   (t < 0),
```

the packet based at divisor clock `h ≥ 0` is `B_h(t) = b_ω(t - h)` on the physical half line.  Its
affine flux `Φ_ω(B_h) = ∫_0^∞ B_h` is finite for every single `h`, and

```text
Φ_ω(B_k) - Φ_ω(B_h) = -c_ω (k - h) .
```

The flux is exact and linear in the clock separation, but it is **not** a bounded functional on the
packet-edge span: at separation `a` the flux of `B_{h+a} - B_h` is `c_ω a` while the packet norm is
only `√(D_ω(a)) ~ c_ω √a`, so the flux-to-norm ratio grows like `√a`.  This is stronger than
unboundedness on ambient `L²`.
-/

open MeasureTheory Set Filter

namespace RHTower

noncomputable section

/-! ### The full-line affine profile -/

/-- The full-line affine profile of the complementary packet: the divisor-clock kernel on the
nonnegative axis, the incoming constant `-c_ω` before it. -/
def affinePacketProfile (ω t : ℝ) : ℝ :=
  if 0 ≤ t then complementaryPacketKernel ω t else -complementaryPacketConstant ω

theorem affinePacketProfile_of_nonneg (ω : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    affinePacketProfile ω t = complementaryPacketKernel ω t := if_pos ht

theorem affinePacketProfile_of_neg (ω : ℝ) {t : ℝ} (ht : t < 0) :
    affinePacketProfile ω t = -complementaryPacketConstant ω := if_neg (not_le.mpr ht)

theorem measurable_affinePacketProfile (ω : ℝ) (hω : 0 ≤ ω) :
    Measurable (affinePacketProfile ω) :=
  Measurable.ite measurableSet_Ici (measurable_complementaryPacketKernel ω hω) measurable_const

theorem integrableOn_affinePacketProfile (ω : ℝ) (hω : 0 ≤ ω) {L : ℝ} (hL : L ≤ 0) :
    IntegrableOn (affinePacketProfile ω) (Ioi L) := by
  have h1 : IntegrableOn (affinePacketProfile ω) (Ioc L 0) := by
    refine Integrable.mono'
      (integrableOn_const
        (C := |complementaryPacketConstant ω| + |complementaryPacketKernel ω 0|)
        (hs := measure_Ioc_lt_top.ne))
      (measurable_affinePacketProfile ω hω).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, affinePacketProfile]
    split_ifs with h
    · have ht0 : t = 0 := le_antisymm ht.2 h
      subst ht0
      have := abs_nonneg (complementaryPacketConstant ω)
      linarith
    · rw [abs_neg]
      have := abs_nonneg (complementaryPacketKernel ω 0)
      linarith
  have h2 : IntegrableOn (affinePacketProfile ω) (Ioi (0 : ℝ)) :=
    (integrableOn_complementaryPacketKernel ω hω).congr_fun
      (fun t ht => (affinePacketProfile_of_nonneg ω (le_of_lt ht)).symm) measurableSet_Ioi
  have hsplit : Ioc L 0 ∪ Ioi (0 : ℝ) = Ioi L := Ioc_union_Ioi_eq_Ioi hL
  rw [← hsplit]
  exact h1.union h2

/-! ### The exact flux -/

/-- The affine flux of the packet based at divisor clock `h`. -/
def affinePacketFlux (ω h : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), affinePacketProfile ω (t - h)

/-- The flux of a single packet splits into the swept incoming constant and the fixed kernel
mass. -/
theorem affinePacketFlux_eq (ω : ℝ) (hω : 0 ≤ ω) {h : ℝ} (hh : 0 ≤ h) :
    affinePacketFlux ω h
      = -(complementaryPacketConstant ω * h)
        + ∫ t in Ioi (0 : ℝ), complementaryPacketKernel ω t := by
  have htrans : (∫ t in Ioi (0 : ℝ), affinePacketProfile ω (t - h))
      = ∫ s in Ioi (-h), affinePacketProfile ω s := by
    have h := setIntegral_Ioi_comp_add_right' (affinePacketProfile ω) 0 (-h)
    simpa [sub_eq_add_neg] using h
  have hint1 : IntegrableOn (affinePacketProfile ω) (Ioc (-h) 0) :=
    (integrableOn_affinePacketProfile ω hω (show -h ≤ 0 by linarith)).mono_set
      Ioc_subset_Ioi_self
  have hint2 : IntegrableOn (affinePacketProfile ω) (Ioi (0 : ℝ)) :=
    (integrableOn_complementaryPacketKernel ω hω).congr_fun
      (fun t ht => (affinePacketProfile_of_nonneg ω (le_of_lt ht)).symm) measurableSet_Ioi
  have hdisj : Disjoint (Ioc (-h) 0) (Ioi (0 : ℝ)) := by
    rw [Set.disjoint_left]
    intro x hx hx2
    exact absurd hx.2 (not_le.mpr hx2)
  have hsplit : Ioc (-h) 0 ∪ Ioi (0 : ℝ) = Ioi (-h) :=
    Ioc_union_Ioi_eq_Ioi (show -h ≤ 0 by linarith)
  have hlow : (∫ s in Ioc (-h) (0 : ℝ), affinePacketProfile ω s)
      = -(complementaryPacketConstant ω * h) := by
    rw [integral_Ioc_eq_integral_Ioo]
    have hcongr : (∫ s in Ioo (-h) (0 : ℝ), affinePacketProfile ω s)
        = ∫ _s in Ioo (-h) (0 : ℝ), -complementaryPacketConstant ω :=
      setIntegral_congr_fun measurableSet_Ioo fun s hs => affinePacketProfile_of_neg ω hs.2
    have hvol : volume.real (Ioo (-h) (0 : ℝ)) = h := by
      rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [hcongr, setIntegral_const, hvol, smul_eq_mul]
    ring
  have hhigh : (∫ s in Ioi (0 : ℝ), affinePacketProfile ω s)
      = ∫ t in Ioi (0 : ℝ), complementaryPacketKernel ω t :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht =>
      affinePacketProfile_of_nonneg ω (le_of_lt ht)
  rw [affinePacketFlux, htrans, ← hsplit, setIntegral_union hdisj measurableSet_Ioi hint1 hint2,
    hlow, hhigh]

/-- **Exact flux theorem.**  The affine flux of a packet difference is the incoming constant times
the clock separation, with no dependence on the kernel. -/
theorem affinePacketFlux_sub (ω : ℝ) (hω : 0 ≤ ω) {h k : ℝ} (hh : 0 ≤ h) (hk : 0 ≤ k) :
    affinePacketFlux ω k - affinePacketFlux ω h
      = -(complementaryPacketConstant ω * (k - h)) := by
  rw [affinePacketFlux_eq ω hω hk, affinePacketFlux_eq ω hω hh]
  ring

/-! ### Unboundedness on the packet-edge span -/

theorem complementaryPacketConstant_pos {ω : ℝ} (hω : 0 ≤ ω) :
    0 < complementaryPacketConstant ω := by
  rw [complementaryPacketConstant]
  positivity

/-- **Affine flux is unbounded on the closed span of its packet-edge domain.**  At separation `a`
the squared flux of `B_{h+a} - B_h` is `c_ω² a²` while its squared norm is `D_ω(a) = c_ω² a + O(1)`,
so the flux-to-norm ratio diverges at rate `√a`. -/
theorem tendsto_affinePacketFlux_sq_div_modulus_atTop (ω : ℝ) (hω : 0 ≤ ω) {h : ℝ} (hh : 0 ≤ h) :
    Tendsto (fun a : ℝ =>
        (affinePacketFlux ω (h + a) - affinePacketFlux ω h) ^ 2
          / packetTranslationModulus (complementaryPacketKernel ω)
              (complementaryPacketConstant ω) a) atTop atTop := by
  have hc := complementaryPacketConstant_pos hω
  have hc2 : (0 : ℝ) < complementaryPacketConstant ω ^ 2 := by positivity
  have hlim := tendsto_complementaryPacketModulus_div ω hω
  have hratio : Tendsto (fun a : ℝ =>
      complementaryPacketConstant ω ^ 2 /
        (packetTranslationModulus (complementaryPacketKernel ω)
          (complementaryPacketConstant ω) a / a)) atTop (nhds 1) := by
    have h := tendsto_const_nhds.div hlim (ne_of_gt hc2)
      (f := fun _ : ℝ => complementaryPacketConstant ω ^ 2)
    rwa [div_self (ne_of_gt hc2)] at h
  have hhalf : ∀ᶠ a : ℝ in atTop,
      (1 : ℝ) / 2 < complementaryPacketConstant ω ^ 2 /
        (packetTranslationModulus (complementaryPacketKernel ω)
          (complementaryPacketConstant ω) a / a) := hratio.eventually_const_lt (by norm_num)
  have hDpos : ∀ᶠ a : ℝ in atTop,
      0 < packetTranslationModulus (complementaryPacketKernel ω)
        (complementaryPacketConstant ω) a / a := hlim.eventually_const_lt hc2
  refine tendsto_atTop_mono' atTop ?_
    (Filter.Tendsto.atTop_mul_const (by norm_num : (0 : ℝ) < 1 / 2) tendsto_id)
  filter_upwards [hhalf, hDpos, eventually_gt_atTop (0 : ℝ)] with a hha hDa hapos
  have hD : 0 < packetTranslationModulus (complementaryPacketKernel ω)
      (complementaryPacketConstant ω) a := by
    have := (div_pos_iff_of_pos_right hapos).mp hDa
    exact this
  have hflux : (affinePacketFlux ω (h + a) - affinePacketFlux ω h) ^ 2
      = complementaryPacketConstant ω ^ 2 * a ^ 2 := by
    rw [affinePacketFlux_sub ω hω hh (by linarith)]
    ring
  have hrewrite : (affinePacketFlux ω (h + a) - affinePacketFlux ω h) ^ 2
      / packetTranslationModulus (complementaryPacketKernel ω)
          (complementaryPacketConstant ω) a
      = a * (complementaryPacketConstant ω ^ 2 /
          (packetTranslationModulus (complementaryPacketKernel ω)
            (complementaryPacketConstant ω) a / a)) := by
    rw [hflux]
    field_simp
  rw [hrewrite]
  have : a * (1 / 2) ≤ a * (complementaryPacketConstant ω ^ 2 /
      (packetTranslationModulus (complementaryPacketKernel ω)
        (complementaryPacketConstant ω) a / a)) :=
    mul_le_mul_of_nonneg_left hha.le hapos.le
  simpa using this

end

end RHTower
