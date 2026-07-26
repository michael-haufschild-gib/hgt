import GaloisForLFunctions.RHTower.ComplementaryPacketPowerSumEnvelope
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Cofinal affine isometry of a boundary packet path

At separation `a` the boundary affine packet path with kernel `k` and incoming constant `c` has
squared distance

```text
D(a) = ∫_0^a (k r + c)^2 dr + ∫_0^∞ (k (r + a) - k r)^2 dr .
```

The first term is the outgoing branch swept by the translation, the second is the translation
modulus of the kernel itself.  If `k` is measurable, integrable and square integrable on the half
line, then

```text
|D(a) - c^2 a| ≤ 5 B + 2 |c| A ,       A ≥ ∫_0^∞ |k| ,  B ≥ ∫_0^∞ k^2 ,
```

uniformly in `a ≥ 0`, and consequently `D(a)/a → c^2`.  No pointwise contraction is claimed and
none is available; the law is cofinal.

The bound depends on `k` only through `A` and `B`, which is what makes it apply uniformly to the
whole boundary family of `ComplementaryPacketPowerSumEnvelope`.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Translation of a half-line integral. -/
theorem setIntegral_Ioi_comp_add_right (g : ℝ → ℝ) (a : ℝ) :
    (∫ r in Ioi (0 : ℝ), g (r + a)) = ∫ s in Ioi a, g s := by
  have hmp : MeasurePreserving (fun r : ℝ => r + a) volume volume :=
    measurePreserving_add_right volume a
  have hme : MeasurableEmbedding (fun r : ℝ => r + a) :=
    (Homeomorph.addRight a).measurableEmbedding
  have hpre : (fun r : ℝ => r + a) ⁻¹' (Ioi a) = Ioi (0 : ℝ) := by
    ext r
    simp
  calc (∫ r in Ioi (0 : ℝ), g (r + a))
      = ∫ r in ((fun r : ℝ => r + a) ⁻¹' (Ioi a)), g (r + a) := by rw [hpre]
    _ = ∫ s in Ioi a, g s := hmp.setIntegral_preimage_emb hme g (Ioi a)

/-- Translation of an integral over a half line with arbitrary base point. -/
theorem setIntegral_Ioi_comp_add_right' (g : ℝ → ℝ) (L a : ℝ) :
    (∫ r in Ioi L, g (r + a)) = ∫ s in Ioi (L + a), g s := by
  have hmp : MeasurePreserving (fun r : ℝ => r + a) volume volume :=
    measurePreserving_add_right volume a
  have hme : MeasurableEmbedding (fun r : ℝ => r + a) :=
    (Homeomorph.addRight a).measurableEmbedding
  have hpre : (fun r : ℝ => r + a) ⁻¹' (Ioi (L + a)) = Ioi L := by
    ext r
    simp
  calc (∫ r in Ioi L, g (r + a))
      = ∫ r in ((fun r : ℝ => r + a) ⁻¹' (Ioi (L + a))), g (r + a) := by rw [hpre]
    _ = ∫ s in Ioi (L + a), g s := hmp.setIntegral_preimage_emb hme g (Ioi (L + a))

/-- The two-point modulus of the boundary affine packet path. -/
def packetTranslationModulus (k : ℝ → ℝ) (c a : ℝ) : ℝ :=
  (∫ r in Ioc (0 : ℝ) a, (k r + c) ^ 2) + ∫ r in Ioi (0 : ℝ), (k (r + a) - k r) ^ 2

section Bounds

variable {k : ℝ → ℝ} {A B c : ℝ}

private theorem integrableOn_translate_sq (hsq : IntegrableOn (fun r => k r ^ 2) (Ioi 0))
    {a : ℝ} (ha : 0 ≤ a) : IntegrableOn (fun r => k (r + a) ^ 2) (Ioi 0) := by
  have hmp : MeasurePreserving (fun r : ℝ => r + a) volume volume :=
    measurePreserving_add_right volume a
  have hme : MeasurableEmbedding (fun r : ℝ => r + a) :=
    (Homeomorph.addRight a).measurableEmbedding
  have hpre : (fun r : ℝ => r + a) ⁻¹' (Ioi a) = Ioi (0 : ℝ) := by
    ext r
    simp
  have hsub : IntegrableOn (fun r => k r ^ 2) (Ioi a) :=
    hsq.mono_set (Ioi_subset_Ioi ha)
  have h := (hmp.integrableOn_comp_preimage hme (f := fun r => k r ^ 2) (s := Ioi a)).2 hsub
  rwa [hpre] at h

/-- The translated square integral is bounded by the original one. -/
theorem setIntegral_translate_sq_le (hsq : IntegrableOn (fun r => k r ^ 2) (Ioi 0))
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ r in Ioi (0 : ℝ), k (r + a) ^ 2) ≤ ∫ r in Ioi (0 : ℝ), k r ^ 2 := by
  rw [setIntegral_Ioi_comp_add_right (fun s => k s ^ 2) a]
  refine setIntegral_mono_set hsq ?_ ?_
  · filter_upwards with r using sq_nonneg _
  · exact Filter.Eventually.of_forall (Ioi_subset_Ioi ha)

/-- The translation modulus of a square-integrable kernel is at most four times its energy. -/
theorem setIntegral_translationModulus_le (hmk : Measurable k)
    (hsq : IntegrableOn (fun r => k r ^ 2) (Ioi 0)) {a : ℝ} (ha : 0 ≤ a) :
    (∫ r in Ioi (0 : ℝ), (k (r + a) - k r) ^ 2) ≤ 4 * ∫ r in Ioi (0 : ℝ), k r ^ 2 := by
  have hta : IntegrableOn (fun r => k (r + a) ^ 2) (Ioi 0) := integrableOn_translate_sq hsq ha
  have hdom : IntegrableOn (fun r => 2 * k (r + a) ^ 2 + 2 * k r ^ 2) (Ioi 0) :=
    (hta.const_mul 2).add (hsq.const_mul 2)
  have hmeas : Measurable fun r : ℝ => (k (r + a) - k r) ^ 2 :=
    (((hmk.comp (measurable_id.add_const a)).sub hmk).pow_const 2)
  have hdiff : IntegrableOn (fun r => (k (r + a) - k r) ^ 2) (Ioi 0) := by
    refine Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
    filter_upwards with r
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (k (r + a) + k r)]
  have hmono : (∫ r in Ioi (0 : ℝ), (k (r + a) - k r) ^ 2)
      ≤ ∫ r in Ioi (0 : ℝ), (2 * k (r + a) ^ 2 + 2 * k r ^ 2) := by
    refine setIntegral_mono_on hdiff hdom measurableSet_Ioi fun r _ => ?_
    nlinarith [sq_nonneg (k (r + a) + k r)]
  have hsplit : (∫ r in Ioi (0 : ℝ), (2 * k (r + a) ^ 2 + 2 * k r ^ 2))
      = 2 * (∫ r in Ioi (0 : ℝ), k (r + a) ^ 2) + 2 * ∫ r in Ioi (0 : ℝ), k r ^ 2 := by
    rw [integral_add (hta.const_mul 2) (hsq.const_mul 2), integral_const_mul, integral_const_mul]
  have htrans := setIntegral_translate_sq_le hsq ha
  rw [hsplit] at hmono
  linarith

end Bounds

/-- **Cofinal affine isometry.**  The two-point modulus of the boundary packet path differs from
the affine profile `c^2 a` by at most `5 B + 2 |c| A`, uniformly in the separation. -/
theorem abs_packetTranslationModulus_sub_le
    {k : ℝ → ℝ} {A B c : ℝ} (hmk : Measurable k)
    (hint : IntegrableOn k (Ioi 0)) (hsq : IntegrableOn (fun r => k r ^ 2) (Ioi 0))
    (hA : (∫ r in Ioi (0 : ℝ), |k r|) ≤ A)
    (hB : (∫ r in Ioi (0 : ℝ), k r ^ 2) ≤ B)
    {a : ℝ} (ha : 0 ≤ a) :
    |packetTranslationModulus k c a - c ^ 2 * a| ≤ 5 * B + 2 * |c| * A := by
  have hIocSub : Ioc (0 : ℝ) a ⊆ Ioi 0 := Ioc_subset_Ioi_self
  have hintIoc : IntegrableOn k (Ioc (0 : ℝ) a) := hint.mono_set hIocSub
  have hsqIoc : IntegrableOn (fun r => k r ^ 2) (Ioc (0 : ℝ) a) := hsq.mono_set hIocSub
  have habs : IntegrableOn (fun r => |k r|) (Ioi 0) := hint.abs
  have hconstIoc : IntegrableOn (fun _ : ℝ => c ^ 2) (Ioc (0 : ℝ) a) :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  -- expand the swept branch
  have hvol : (volume.real (Ioc (0 : ℝ) a)) = a := by
    rw [Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal ha]
  have hexpand : (∫ r in Ioc (0 : ℝ) a, (k r + c) ^ 2)
      = (∫ r in Ioc (0 : ℝ) a, k r ^ 2) + 2 * c * (∫ r in Ioc (0 : ℝ) a, k r) + c ^ 2 * a := by
    calc (∫ r in Ioc (0 : ℝ) a, (k r + c) ^ 2)
        = ∫ r in Ioc (0 : ℝ) a, (k r ^ 2 + (2 * c) * k r + c ^ 2) :=
          setIntegral_congr_fun measurableSet_Ioc fun r _ => by ring
      _ = (∫ r in Ioc (0 : ℝ) a, (k r ^ 2 + (2 * c) * k r)) + ∫ _r in Ioc (0 : ℝ) a, c ^ 2 :=
          integral_add (by exact hsqIoc.add (hintIoc.const_mul (2 * c))) hconstIoc
      _ = (∫ r in Ioc (0 : ℝ) a, k r ^ 2) + (2 * c) * (∫ r in Ioc (0 : ℝ) a, k r)
            + ∫ _r in Ioc (0 : ℝ) a, c ^ 2 := by
          rw [integral_add hsqIoc (hintIoc.const_mul (2 * c)), integral_const_mul]
      _ = (∫ r in Ioc (0 : ℝ) a, k r ^ 2) + 2 * c * (∫ r in Ioc (0 : ℝ) a, k r) + c ^ 2 * a := by
          rw [setIntegral_const, hvol, smul_eq_mul]
          ring
  -- the three pieces
  have hsq0 : 0 ≤ ∫ r in Ioc (0 : ℝ) a, k r ^ 2 :=
    setIntegral_nonneg measurableSet_Ioc fun r _ => sq_nonneg _
  have hsqle : (∫ r in Ioc (0 : ℝ) a, k r ^ 2) ≤ B := by
    refine le_trans (setIntegral_mono_set hsq ?_ ?_) hB
    · filter_upwards with r using sq_nonneg _
    · exact Filter.Eventually.of_forall hIocSub
  have habsle : |∫ r in Ioc (0 : ℝ) a, k r| ≤ A := by
    refine le_trans (abs_integral_le_integral_abs) ?_
    refine le_trans (setIntegral_mono_set habs ?_ ?_) hA
    · filter_upwards with r using abs_nonneg _
    · exact Filter.Eventually.of_forall hIocSub
  have htrans0 : 0 ≤ ∫ r in Ioi (0 : ℝ), (k (r + a) - k r) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun r _ => sq_nonneg _
  have htransle : (∫ r in Ioi (0 : ℝ), (k (r + a) - k r) ^ 2) ≤ 4 * B := by
    refine le_trans (setIntegral_translationModulus_le hmk hsq ha) ?_
    linarith
  have hAnonneg : 0 ≤ A :=
    le_trans (setIntegral_nonneg measurableSet_Ioi fun r _ => abs_nonneg _) hA
  have hprod : |2 * c * (∫ r in Ioc (0 : ℝ) a, k r)| ≤ 2 * |c| * A := by
    have h2c : (0 : ℝ) ≤ 2 * |c| := by positivity
    calc |2 * c * (∫ r in Ioc (0 : ℝ) a, k r)|
        = 2 * |c| * |∫ r in Ioc (0 : ℝ) a, k r| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * |c| * A := mul_le_mul_of_nonneg_left habsle h2c
  rw [packetTranslationModulus, hexpand,
    show (∫ r in Ioc (0 : ℝ) a, k r ^ 2) + 2 * c * (∫ r in Ioc (0 : ℝ) a, k r) + c ^ 2 * a +
        (∫ r in Ioi (0 : ℝ), (k (r + a) - k r) ^ 2) - c ^ 2 * a
        = (∫ r in Ioc (0 : ℝ) a, k r ^ 2) + 2 * c * (∫ r in Ioc (0 : ℝ) a, k r) +
          ∫ r in Ioi (0 : ℝ), (k (r + a) - k r) ^ 2 by ring]
  refine le_trans (abs_add_three _ _ _) ?_
  rw [abs_of_nonneg hsq0, abs_of_nonneg htrans0]
  linarith

/-- **Cofinal slope.**  The two-point modulus has affine slope `c ^ 2` at infinity. -/
theorem tendsto_packetTranslationModulus_div
    {k : ℝ → ℝ} {A B c : ℝ} (hmk : Measurable k)
    (hint : IntegrableOn k (Ioi 0)) (hsq : IntegrableOn (fun r => k r ^ 2) (Ioi 0))
    (hA : (∫ r in Ioi (0 : ℝ), |k r|) ≤ A)
    (hB : (∫ r in Ioi (0 : ℝ), k r ^ 2) ≤ B) :
    Filter.Tendsto (fun a : ℝ => packetTranslationModulus k c a / a) Filter.atTop
      (nhds (c ^ 2)) := by
  have hlim : Filter.Tendsto (fun a : ℝ => (5 * B + 2 * |c| * A) / a) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with a ha
  have h := abs_packetTranslationModulus_sub_le (c := c) hmk hint hsq hA hB ha.le
  have hkey : packetTranslationModulus k c a / a - c ^ 2
      = (packetTranslationModulus k c a - c ^ 2 * a) / a := by
    field_simp
  rw [Real.norm_eq_abs, hkey, abs_div, abs_of_pos ha]
  gcongr

end

end RHTower
