import GaloisForLFunctions.BiScaleUncertainty.FiniteTranslationTrains
import GaloisForLFunctions.BiScaleUncertainty.UnitEnergySmallSources
import GaloisForLFunctions.HTGeometry.L2TranslationExponentialIndependence
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Finite cross-sample cancellation with actual smooth sources

A nonzero smooth compact source admits another smooth source, supported in twice
its prescribed radius, whose cross-correlation vanishes at any finite collection
of samples but is not identically zero. Rank–nullity supplies coefficients and
the existing L² translate-independence theorem proves the response survives.

The second part records the exact correlation and energy formulas for combining
two independently chosen source shapes at a distant separation. These are
construction ingredients; no full logarithmic-grid obstruction is asserted here.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty.FiniteNullCorrector
noncomputable section
set_option autoImplicit false

private theorem finite_constraints (n : ℕ) (u : Fin (n + 1) → ℝ → ℝ) (z : Fin n → ℝ) :
    ∃ c : Fin (n + 1) → ℝ, c ≠ 0 ∧ ∀ k, ∑ i, c i * u i (z k) = 0 := by
  let A : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun c k => ∑ i, c i * u i (z k)
      map_add' := by
        intro c d
        funext k
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        funext k
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum] }
  have hd : Module.finrank ℝ (Fin n → ℝ) < Module.finrank ℝ (Fin (n + 1) → ℝ) := by
    simp only [Module.finrank_pi, Fintype.card_fin]
    omega
  obtain ⟨c, hc, hcn⟩ := A.ker.ne_bot_iff.mp (LinearMap.ker_ne_bot_of_finrank_lt hd)
  refine ⟨c, hcn, ?_⟩
  intro k
  exact congrFun hc k

private theorem translate_sum_nonzero {n : ℕ} {h : ℝ → ℝ}
    (hh : Continuous h) (hhc : HasCompactSupport h) (hhn : ∃ x, h x ≠ 0)
    (s : Fin n → ℝ) (hs : Function.Injective s) (c : Fin n → ℝ) (hc : c ≠ 0) :
    ∃ x, ∑ i, c i * h (x - s i) ≠ 0 := by
  let H : ℝ → ℂ := fun x => (h x : ℂ)
  have hHc : Continuous H := Complex.continuous_ofReal.comp hh
  have hHcs : HasCompactSupport H := hhc.comp_left Complex.ofReal_zero
  have hH2 : MemLp H 2 (volume : Measure ℝ) := hHc.memLp_of_hasCompactSupport hHcs
  let F : Lp ℂ 2 (volume : Measure ℝ) := hH2.toLp H
  have hFn : F ≠ 0 := by
    intro hz
    have hae : H =ᵐ[volume] 0 :=
      hH2.coeFn_toLp.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hz)
    have hzero := Measure.eq_of_ae_eq hae hHc continuous_const
    obtain ⟨x, hx⟩ := hhn
    apply hx
    exact Complex.ofReal_eq_zero.mp (congrFun hzero x)
  have hsi : Function.Injective (fun i => -s i) := by
    intro i j hij
    exact hs (neg_injective hij)
  have hli := HTGeometry.linearIndependent_L2_translates (fun i => -s i) hsi hFn
  by_contra! hz
  have hterms (i : Fin n) :
      ((RHTower.MellinL2.additiveTranslationUnitary (-s i) F : Lp ℂ 2 volume) : ℝ → ℂ)
        =ᵐ[volume] fun x => (h (x - s i) : ℂ) := by
    filter_upwards [Lp.coeFn_compMeasurePreserving F
      (RHTower.MellinL2.realTranslation_measurePreserving (-s i)),
      hH2.coeFn_toLp.comp_tendsto
        (RHTower.MellinL2.realTranslation_measurePreserving (-s i)).quasiMeasurePreserving.tendsto_ae]
      with x ha hb
    change RHTower.MellinL2.additiveTranslationUnitary (-s i) F x = F (x + -s i) at ha
    change F (x + -s i) = (h (x + -s i) : ℂ) at hb
    simpa only [sub_eq_add_neg] using ha.trans hb
  have hscaled (i : Fin n) :
      (((c i : ℂ) • RHTower.MellinL2.additiveTranslationUnitary (-s i) F : Lp ℂ 2 volume) : ℝ → ℂ)
        =ᵐ[volume] fun x => (c i : ℂ) * (h (x - s i) : ℂ) := by
    filter_upwards [Lp.coeFn_smul (c i : ℂ)
      (RHTower.MellinL2.additiveTranslationUnitary (-s i) F), hterms i] with x ha hb
    simpa only [Pi.smul_apply, smul_eq_mul, hb] using ha
  have hsum : (∑ i, (c i : ℂ) • RHTower.MellinL2.additiveTranslationUnitary (-s i) F) = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun i => (c i : ℂ) • RHTower.MellinL2.additiveTranslationUnitary (-s i) F),
      ae_all_iff.mpr hscaled] with x ha hb
    calc
      _ = ∑ i, ((c i : ℂ) • RHTower.MellinL2.additiveTranslationUnitary (-s i) F : Lp ℂ 2 volume) x := by
        simpa only [Finset.sum_apply] using ha
      _ = ∑ i, (c i : ℂ) * (h (x - s i) : ℂ) := Finset.sum_congr rfl (fun i _ => hb i)
      _ = 0 := by exact_mod_cast hz x
  apply hc
  funext i
  exact Complex.ofReal_eq_zero.mp ((Fintype.linearIndependent_iff.mp hli)
    (fun j => (c j : ℂ)) hsum i)

def cross (f g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ u, f u * g (u + x)

theorem cross_finiteTranslate {n : ℕ} {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (c s : Fin n → ℝ) (x : ℝ) :
    cross f (finiteTranslateSource f Finset.univ c s) x =
      ∑ i, c i * autocorr f (x - s i) := by
  let W := fun i u => c i * (f u * f (u + (x - s i)))
  have hi (i : Fin n) : Integrable (W i) := by
    simpa only [W, add_zero] using
      (integrable_shift_mul_shift hf hfc 0 (x - s i)).const_mul (c i)
  have he : (fun u => f u * finiteTranslateSource f Finset.univ c s (u + x)) =
      fun u => ∑ i, W i u := by
    funext u
    simp only [finiteTranslateSource, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [W]
    rw [show u + x - s i = u + (x - s i) by ring]
    ring
  unfold cross
  rw [he, integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_const_mul (c i) _

/-- Finite prescribed cross samples vanish for a nonzero response from an actual
smooth corrector supported within a fixed interval. -/
theorem exists_smooth_corrector {f : ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ u, r < |u| → f u = 0) (n : ℕ) (z : Fin n → ℝ) :
    ∃ v : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) v ∧ HasCompactSupport v ∧
      (∀ u, 2 * r < |u| → v u = 0) ∧
      (∀ k, cross f v (z k) = 0) ∧ ∃ x, cross f v x ≠ 0 := by
  let d := r / ((n : ℝ) + 1)
  have hd : 0 < d := by dsimp only [d]; positivity
  let s : Fin (n + 1) → ℝ := fun i => d * (i : ℕ)
  have hsi : Function.Injective s := by
    intro i j hij
    have he : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by
      change d * (i : ℕ) = d * (j : ℕ) at hij
      nlinarith only [hij, hd]
    exact Fin.ext (by exact_mod_cast he)
  have hs (i : Fin (n + 1)) : |s i| ≤ r := by
    have hi : ((i : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast i.isLt.le
    have hs0 : 0 ≤ s i := mul_nonneg hd.le (Nat.cast_nonneg _)
    have he : d * ((n : ℝ) + 1) = r := by
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      dsimp only [d]
      field_simp
    rw [abs_of_nonneg hs0]
    change d * (i : ℕ) ≤ r
    nlinarith only [hi, hd, he]
  obtain ⟨c, hc, hzero⟩ := finite_constraints n (fun i x => autocorr f (x - s i)) z
  let v := finiteTranslateSource f Finset.univ c s
  have hv := contDiff_finiteTranslateSource hf Finset.univ c s
  have hvc := hasCompactSupport_finiteTranslateSource hfc Finset.univ c s
  refine ⟨v, hv, hvc, ?_, ?_, ?_⟩
  · intro u hu
    apply Finset.sum_eq_zero
    intro i _
    have hdist : r < |u - s i| := by
      have ht : |u| ≤ |u - s i| + |s i| := by
        simpa only [sub_add_cancel] using abs_add_le (u - s i) (s i)
      linarith only [hu, ht, hs i]
    simp only [hsupp (u - s i) hdist, mul_zero]
  · intro k
    exact (cross_finiteTranslate hf.continuous hfc c s (z k)).trans (hzero k)
  · have hcont : Continuous (autocorr f) := continuous_autocorr_compact ⟨⟨f, hf.continuous⟩, hfc⟩
    obtain ⟨x, hx⟩ := translate_sum_nonzero hcont (hasCompactSupport_autocorr hfc)
      ⟨0, hR.ne'⟩ s hsi c hc
    exact ⟨x, by simpa only [v, cross_finiteTranslate hf.continuous hfc] using hx⟩

end
end GaloisForLFunctions.BiScaleUncertainty.FiniteNullCorrector

namespace GaloisForLFunctions.BiScaleUncertainty.SeparatedSourcePair
noncomputable section
set_option autoImplicit false
open FiniteNullCorrector

theorem cross_eq_zero_of_source_radii {f g : ℝ → ℝ} {A B x : ℝ}
    (hf : ∀ u, A < |u| → f u = 0) (hg : ∀ u, B < |u| → g u = 0)
    (hx : A + B < |x|) : cross f g x = 0 := by
  have hz : ∀ u, f u * g (u + x) = 0 := by
    intro u
    by_cases hu : f u = 0
    · simp only [hu, zero_mul]
    by_cases hv : g (u + x) = 0
    · simp only [hv, mul_zero]
    have ha : |u| ≤ A := le_of_not_gt (fun h => hu (hf u h))
    have hb : |u + x| ≤ B := le_of_not_gt (fun h => hv (hg (u + x) h))
    have ht : |x| ≤ |u + x| + |u| := by
      simpa only [show u + x - u = x by ring] using abs_sub (u + x) u
    exfalso
    linarith only [ha, hb, ht, hx]
  simp only [cross, hz, integral_zero]

theorem cross_swap (f g : ℝ → ℝ) (x : ℝ) : cross g f x = cross f g (-x) := by
  unfold cross
  rw [← integral_add_right_eq_self (μ := volume) (fun u => f u * g (u + -x)) x]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [show u + x + -x = u by ring]
  ring

private theorem integrable_cross {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (x : ℝ) : Integrable (fun u => f u * g (u + x)) :=
  (hf.mul (hg.comp (continuous_add_const x))).integrable_of_hasCompactSupport hfc.mul_right

theorem autocorr_add_cross {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (x : ℝ) :
    autocorr (fun u => f u + g u) x =
      autocorr f x + autocorr g x + cross f g x + cross f g (-x) := by
  have hff := integrable_cross hf hf hfc x
  have hgg := integrable_cross hg hg hgc x
  have hfg := integrable_cross hf hg hfc x
  have hgf := integrable_cross hg hf hgc x
  have he : (fun u => (f u + g u) * (f (u + x) + g (u + x))) =
      fun u => (f u * f (u + x) + g u * g (u + x)) +
        (f u * g (u + x) + g u * f (u + x)) := by
    funext u
    ring
  change (∫ u, (f u + g u) * (f (u + x) + g (u + x))) = _
  have hsplit := integral_add (hff.add hgg) (hfg.add hgf)
  simp only [Pi.add_apply] at hsplit
  rw [he, hsplit,
    integral_add hff hgg, integral_add hfg hgf]
  change autocorr f x + autocorr g x + (cross f g x + cross g f x) = _
  rw [cross_swap f g x]
  ring

def source (f g : ℝ → ℝ) (a T u : ℝ) : ℝ := f u + a * sourceTranslate g T u

theorem source_smooth {f g : ℝ → ℝ} {r : WithTop ℕ∞}
    (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) (a T : ℝ) :
    ContDiff ℝ r (source f g a T) :=
  hf.add (contDiff_const.mul (hg.comp (contDiff_id.sub contDiff_const)))

theorem source_compact {f g : ℝ → ℝ} (hfc : HasCompactSupport f)
    (hgc : HasCompactSupport g) (a T : ℝ) : HasCompactSupport (source f g a T) :=
  hfc.add (hgc.comp_homeomorph (Homeomorph.subRight T)).mul_left

theorem cross_scaled_translate (f g : ℝ → ℝ) (a T x : ℝ) :
    cross f (fun u => a * sourceTranslate g T u) x = a * cross f g (x - T) := by
  unfold cross sourceTranslate
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [show u + x - T = u + (x - T) by ring]
  ring

/-- Exact three-packet expansion for two independently chosen actual source shapes. -/
theorem source_correlation {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (a T x : ℝ) :
    autocorr (source f g a T) x = autocorr f x + a ^ 2 * autocorr g x +
      a * cross f g (x - T) + a * cross f g (-x - T) := by
  have htg : Continuous (fun u => a * sourceTranslate g T u) :=
    continuous_const.mul (hg.comp (continuous_id.sub continuous_const))
  have htgc : HasCompactSupport (fun u => a * sourceTranslate g T u) :=
    (hgc.comp_homeomorph (Homeomorph.subRight T)).mul_left
  change autocorr (fun u => f u + a * sourceTranslate g T u) x = _
  rw [autocorr_add_cross hf htg hfc htgc, autocorr_source_const_mul,
    autocorr_sourceTranslate, cross_scaled_translate, cross_scaled_translate]

/-- The exact source-energy parallelogram is preserved by translation and scaling. -/
theorem source_energy_pair {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (a T : ℝ) :
    biScaleLevyEnergy (source f g a T) + biScaleLevyEnergy (source f g (-a) T) =
      2 * (biScaleLevyEnergy f + a ^ 2 * biScaleLevyEnergy g) := by
  have htg : ContDiff ℝ 2 (fun u => a * sourceTranslate g T u) :=
    contDiff_const.mul (hg.comp (contDiff_id.sub contDiff_const))
  have htgc : HasCompactSupport (fun u => a * sourceTranslate g T u) :=
    (hgc.comp_homeomorph (Homeomorph.subRight T)).mul_left
  have hp := biScaleLevyEnergy_source_parallelogram hf htg hfc htgc
  have he : (fun u => f u - a * sourceTranslate g T u) = source f g (-a) T := by
    funext u
    unfold source
    ring
  rw [he, biScaleLevyEnergy_source_const_mul, biScaleLevyEnergy_sourceTranslate] at hp
  exact hp

end
end GaloisForLFunctions.BiScaleUncertainty.SeparatedSourcePair
