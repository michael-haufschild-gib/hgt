import GaloisForLFunctions.RHTower.SoninDilationSourceSupportRecovery

/-!
# Exact support recovery for coherent finite Sonin sources

A nonzero outermost dilation coefficient cannot be canceled by smaller dilation
scales on a bounded physical band. Exact finite support descent therefore recovers
the input radius `c/R` from an output radius `c`. Fourier covariance and uncertainty
extend this law to the sum of the physical and Fourier forbidden bands.

Every finite complex packet is reduced by combining equal scales and removing
zero coefficients. Thus retained compression is injective on a lost Sonin layer
for every nonzero coherent source in the crossing chamber. No uniform separation
of scales or cofinal completion is assumed.
-/

noncomputable section
namespace RHTower
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace

/-- Literal finite complex packet of symmetric normalized dilations. -/
def soninFiniteDilationSource {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ i, 1 < r i) (u : ι → ℂ) : SoninL2 →L[ℂ] SoninL2 :=
  ∑ i ∈ s, u i • dilationSum (r i) (hr i)

private theorem physical_inverse_of_outermost
    {R S b c : ℝ} (hR : 0 < R) (hS : 0 < S) (hSR : S < R) (hc : 0 < c)
    (H V : SoninL2 →L[ℂ] SoninL2) {u : ℂ} (hu : u ≠ 0)
    (hH : ∀ f, H f = u • dilation R⁻¹ (inv_pos.mpr hR) f + V f)
    (hV : ∀ t, 0 ≤ t → ∀ f, f ∈ centralPhysicalForbidden t →
      V f ∈ centralPhysicalForbidden (S * t))
    {f : SoninL2} (hf : f ∈ centralPhysicalForbidden b)
    (hHf : H f ∈ centralPhysicalForbidden c) :
    f ∈ centralPhysicalForbidden (c / R) := by
  have hq : 1 < R / S := (one_lt_div hS).mpr hSR
  have hd : 0 < c / R := div_pos hc hR
  have descent (t : ℝ) (ht : 0 ≤ t) (hct : c ≤ R * t)
      (hf' : f ∈ centralPhysicalForbidden ((R / S) * t)) :
      f ∈ centralPhysicalForbidden t := by
    have htail : V f ∈ centralPhysicalForbidden (R * t) := by
      have h := hV ((R / S) * t) (mul_nonneg (div_pos hR hS).le ht) f hf'
      have heq : S * ((R / S) * t) = R * t := by field_simp
      exact heq ▸ h
    have houter : dilation R⁻¹ (inv_pos.mpr hR) f ∈ centralPhysicalForbidden (R * t) := by
      apply (centralPhysicalForbidden _).smul_mem_iff hu |>.mp
      have h := (centralPhysicalForbidden (R * t)).sub_mem
        (centralPhysicalForbidden_mono hct hHf) htail
      simpa only [hH, add_sub_cancel_right] using h
    have h := dilation_mem_centralPhysicalForbidden hR houter
    simpa only [dilation_dilation_inv, mul_div_cancel_left₀ _ hR.ne'] using h
  have hiter : ∀ n : ℕ,
      f ∈ centralPhysicalForbidden ((R / S) ^ n * (c / R)) →
      f ∈ centralPhysicalForbidden (c / R) := by
    intro n
    induction n with
    | zero => simp only [pow_zero, one_mul, imp_self]
    | succ n ih =>
      intro hn
      apply ih
      apply descent _ (mul_nonneg (pow_nonneg (div_pos hR hS).le _) hd.le)
      · calc c = R * (c / R) := by field_simp
             _ ≤ R * ((R / S) ^ n * (c / R)) :=
               mul_le_mul_of_nonneg_left
                 (le_mul_of_one_le_left hd.le (one_le_pow₀ hq.le)) hR.le
      · have heq : (R / S) ^ (n + 1) * (c / R) =
            (R / S) * ((R / S) ^ n * (c / R)) := by rw [pow_succ]; ring
        exact heq ▸ hn
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (b / (c / R)) hq
  exact hiter n (centralPhysicalForbidden_mono ((div_lt_iff₀ hd).mp hn).le hf)

/-- Fourier transform retains every coefficient of the finite symmetric source. -/
theorem fourierUnitary_soninFiniteDilationSource {ι : Type*} (s : Finset ι)
    (r : ι → ℝ) (hr : ∀ i, 1 < r i) (u : ι → ℂ) (f : SoninL2) :
    fourierUnitary (soninFiniteDilationSource s r hr u f) =
      soninFiniteDilationSource s r hr u (fourierUnitary f) := by
  simp only [soninFiniteDilationSource, _root_.sum_apply,
    _root_.smul_apply, map_sum, map_smul, fourierUnitary_dilationSum]

/-- A finite packet transports a physical band by at most its largest scale. -/
theorem soninFiniteDilationSource_mem_physical {ι : Type*} (s : Finset ι)
    (r : ι → ℝ) (hr : ∀ i, 1 < r i) (u : ι → ℂ) {b R : ℝ}
    (hb : 0 ≤ b) (hR : ∀ i ∈ s, r i ≤ R) {f : SoninL2}
    (hf : f ∈ centralPhysicalForbidden b) :
    soninFiniteDilationSource s r hr u f ∈ centralPhysicalForbidden (R * b) := by
  simp only [soninFiniteDilationSource, _root_.sum_apply, _root_.smul_apply]
  apply (centralPhysicalForbidden _).sum_mem
  intro i hi
  exact (centralPhysicalForbidden _).smul_mem _
    (centralPhysicalForbidden_mono (mul_le_mul_of_nonneg_right (hR i hi) hb)
      (dilationSum_mem_centralPhysicalForbidden hb (hr i) hf))

/-- Exact physical support recovery at a unique maximal active source scale. -/
theorem mem_physical_of_soninFiniteDilationSource {ι : Type*} (s : Finset ι)
    (r : ι → ℝ) (hr : ∀ i, 1 < r i) (u : ι → ℂ) {k : ι}
    (hk : k ∈ s) (hu : u k ≠ 0) (hmax : ∀ i ∈ s, i ≠ k → r i < r k)
    {b c : ℝ} (hc : 0 < c) {f : SoninL2}
    (hf : f ∈ centralPhysicalForbidden b)
    (hHf : soninFiniteDilationSource s r hr u f ∈ centralPhysicalForbidden c) :
    f ∈ centralPhysicalForbidden (c / r k) := by
  classical
  let scales := insert (1 : ℝ) ((s.erase k).image r)
  have hne : scales.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let S := scales.sup' hne id
  have hS1 : 1 ≤ S := Finset.le_sup' id (Finset.mem_insert_self _ _)
  have hSR : S < r k := by
    apply (Finset.sup'_lt_iff hne).mpr
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hr k
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hmax i (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hi).1
  have hSi : ∀ i ∈ s.erase k, r i ≤ S := by
    intro i hi
    exact Finset.le_sup' id (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  let V : SoninL2 →L[ℂ] SoninL2 :=
    u k • dilationCLM (r k) (zero_lt_one.trans (hr k)) +
      soninFiniteDilationSource (s.erase k) r hr u
  apply physical_inverse_of_outermost (zero_lt_one.trans (hr k))
    (zero_lt_one.trans_le hS1) hSR hc (soninFiniteDilationSource s r hr u) V hu
    (f := f) (b := b)
  · intro w
    have hsum := Finset.sum_erase_add s (fun i => u i • dilationSum (r i) (hr i)) hk
    have heq := congrArg (fun A : SoninL2 →L[ℂ] SoninL2 => A w) hsum
    simp only [_root_.add_apply, _root_.smul_apply,
      dilationSum_apply] at heq
    dsimp only [V, soninFiniteDilationSource]
    rw [← heq]
    simp only [_root_.add_apply, _root_.smul_apply,
      dilationCLM_apply, smul_add]
    abel
  · intro t ht w hw
    change u k • dilation (r k) (zero_lt_one.trans (hr k)) w +
      soninFiniteDilationSource (s.erase k) r hr u w ∈ centralPhysicalForbidden (S * t)
    apply (centralPhysicalForbidden _).add_mem
    · apply (centralPhysicalForbidden _).smul_mem
      apply centralPhysicalForbidden_mono (show t / r k ≤ S * t from ?_)
        (dilation_mem_centralPhysicalForbidden (zero_lt_one.trans (hr k)) hw)
      calc t / r k ≤ t := div_le_self ht (hr k).le
           _ ≤ S * t := le_mul_of_one_le_left ht hS1
    · exact soninFiniteDilationSource_mem_physical _ r hr u ht hSi hw
  · exact hf
  · exact hHf

private theorem mem_fourier_iff_physical {a : ℝ} {f : SoninL2} :
    f ∈ centralFourierForbidden a ↔ fourierUnitary f ∈ centralPhysicalForbidden a :=
  mem_fourierForbidden_iff (centralInterval a) (measurableSet_centralInterval a) f

/-- The finite complex source has the same outer support law in the Fourier polarization. -/
theorem soninFiniteDilationSource_mem_fourier {ι : Type*} (s : Finset ι)
    (r : ι → ℝ) (hr : ∀ i, 1 < r i) (u : ι → ℂ) {b R : ℝ}
    (hb : 0 ≤ b) (hR : ∀ i ∈ s, r i ≤ R) {f : SoninL2}
    (hf : f ∈ centralFourierForbidden b) :
    soninFiniteDilationSource s r hr u f ∈ centralFourierForbidden (R * b) := by
  rw [mem_fourier_iff_physical, fourierUnitary_soninFiniteDilationSource]
  exact soninFiniteDilationSource_mem_physical s r hr u hb hR (mem_fourier_iff_physical.mp hf)

/-- Exact Fourier support recovery retains all coherent coefficients. -/
theorem mem_fourier_of_soninFiniteDilationSource {ι : Type*} (s : Finset ι)
    (r : ι → ℝ) (hr : ∀ i, 1 < r i) (u : ι → ℂ) {k : ι}
    (hk : k ∈ s) (hu : u k ≠ 0) (hmax : ∀ i ∈ s, i ≠ k → r i < r k)
    {b c : ℝ} (hc : 0 < c) {f : SoninL2}
    (hf : f ∈ centralFourierForbidden b)
    (hHf : soninFiniteDilationSource s r hr u f ∈ centralFourierForbidden c) :
    f ∈ centralFourierForbidden (c / r k) := by
  rw [mem_fourier_iff_physical] at hf hHf ⊢
  rw [fourierUnitary_soninFiniteDilationSource] at hHf
  exact mem_physical_of_soninFiniteDilationSource s r hr u hk hu hmax hc hf hHf

/-- Exact inverse support for a coherent source with a unique largest active scale. -/
theorem soninFiniteDilationSource_mem_forbiddenSum_iff {ι : Type*} (s : Finset ι)
    (r : ι → ℝ) (hr : ∀ i, 1 < r i) (u : ι → ℂ) {k : ι}
    (hk : k ∈ s) (hu : u k ≠ 0) (hmax : ∀ i ∈ s, i ≠ k → r i < r k)
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c) {v : SoninL2}
    (hv : v ∈ centralPhysicalForbidden b ⊔ centralFourierForbidden b) :
    soninFiniteDilationSource s r hr u v ∈ centralPhysicalForbidden c ⊔ centralFourierForbidden c ↔
      v ∈ centralPhysicalForbidden (c / r k) ⊔ centralFourierForbidden (c / r k) := by
  have hbound : ∀ i ∈ s, r i ≤ r k := by
    intro i hi
    by_cases hik : i = k
    · subst i; exact le_rfl
    · exact (hmax i hi hik).le
  let H := soninFiniteDilationSource s r hr u
  constructor
  · intro hD
    obtain ⟨f, hf, g, hg, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨h, hh, j, hj, heq⟩ := Submodule.mem_sup.mp hD
    have hsum : H f + H g = h + j := by simpa only [map_add] using heq.symm
    have hsep : H f - h = j - H g := by
      calc _ = (H f + H g) - (h + H g) := by abel
           _ = (h + j) - (h + H g) := by rw [hsum]
           _ = _ := by abel
    have hz : H f - h = 0 := by
      apply eq_zero_of_mem_centralPhysicalForbidden_of_mem_centralFourierForbidden
        (a := max (r k * b) c) (b := max (r k * b) c)
      · exact (centralPhysicalForbidden _).sub_mem
          (centralPhysicalForbidden_mono (le_max_left _ _)
            (soninFiniteDilationSource_mem_physical s r hr u hb.le hbound hf))
          (centralPhysicalForbidden_mono (le_max_right _ _) hh)
      · rw [hsep]
        exact (centralFourierForbidden _).sub_mem
          (centralFourierForbidden_mono (le_max_right _ _) hj)
          (centralFourierForbidden_mono (le_max_left _ _)
            (soninFiniteDilationSource_mem_fourier s r hr u hb.le hbound hg))
    have hHf : H f = h := sub_eq_zero.mp hz
    have hHg : H g = j := by rw [hHf] at hsum; exact add_left_cancel hsum
    exact Submodule.mem_sup.mpr ⟨f,
      mem_physical_of_soninFiniteDilationSource s r hr u hk hu hmax hc hf (hHf.symm ▸ hh),
      g, mem_fourier_of_soninFiniteDilationSource s r hr u hk hu hmax hc hg (hHg.symm ▸ hj), rfl⟩
  · intro hv'
    obtain ⟨f, hf, g, hg, rfl⟩ := Submodule.mem_sup.mp hv'
    have hr0 : 0 < r k := zero_lt_one.trans (hr k)
    have hrc : r k * (c / r k) = c := by field_simp
    rw [map_add]
    exact Submodule.mem_sup.mpr ⟨_,
      hrc ▸ soninFiniteDilationSource_mem_physical s r hr u (div_pos hc hr0).le hbound hf,
      _, hrc ▸ soninFiniteDilationSource_mem_fourier s r hr u (div_pos hc hr0).le hbound hg, rfl⟩

/-- Every finite packet has an exact reduction combining repeated scales and deleting zero weights. -/
theorem exists_reduced_soninFiniteDilationSource {ι : Type*} (s : Finset ι)
    (r : ι → ℝ) (hr : ∀ i, 1 < r i) (u : ι → ℂ) :
    ∃ (t : Finset {x : ℝ // 1 < x}) (w : {x : ℝ // 1 < x} → ℂ),
      (∀ q ∈ t, w q ≠ 0) ∧ (∀ q ∈ t, ∃ i ∈ s, r i = q.1) ∧
      soninFiniteDilationSource s r hr u =
        soninFiniteDilationSource t Subtype.val (fun q => q.2) w := by
  classical
  let ρ : ι → {x : ℝ // 1 < x} := fun i => ⟨r i, hr i⟩
  let w : {x : ℝ // 1 < x} → ℂ := fun q => ∑ i ∈ s with ρ i = q, u i
  let t := (s.image ρ).filter (fun q => w q ≠ 0)
  refine ⟨t, w, ?_, ?_, ?_⟩
  · intro q hq
    exact (Finset.mem_filter.mp hq).2
  · intro q hq
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hq).1
    exact ⟨i, hi, congrArg Subtype.val heq⟩
  · have hgroup := Finset.sum_fiberwise_of_maps_to
      (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩ : ∀ i ∈ s, ρ i ∈ s.image ρ)
      (fun i => u i • dilationSum (r i) (hr i))
    unfold soninFiniteDilationSource
    rw [← hgroup]
    calc
      _ = ∑ q ∈ s.image ρ, w q • dilationSum q.1 q.2 := by
        apply Finset.sum_congr rfl
        intro q hq
        dsimp only [w]
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro i hi
        have heq := (Finset.mem_filter.mp hi).2
        have hval : r i = q.1 := congrArg Subtype.val heq
        congr 2
      _ = ∑ q ∈ t, w q • dilationSum q.1 q.2 := by
        dsimp only [t]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro q hq
        by_cases hw : w q = 0 <;> simp [hw]

/-- A nonzero coherent source cannot annihilate a lost-layer vector after retained compression.
Repeated scales and all exact coefficient cancellations are handled internally. -/
theorem eq_zero_of_soninFiniteDilationSource_retained_eq_zero {ι : Type*} (s : Finset ι)
    (r : ι → ℝ) (hr : ∀ i, 1 < r i) (u : ι → ℂ)
    {a b c : ℝ} (hb : 0 < b) (hc : 0 < c) (hcross : ∀ i ∈ s, c ≤ r i * a)
    (hH : soninFiniteDilationSource s r hr u ≠ 0) {v : SoninL2}
    (hva : v ∈ centralSoninCarrier a) (hvb : centralSoninProjection b v = 0)
    (hvH : centralSoninProjection c (soninFiniteDilationSource s r hr u v) = 0) : v = 0 := by
  classical
  obtain ⟨t, w, hw, horigin, heq⟩ := exists_reduced_soninFiniteDilationSource s r hr u
  have hne : t.Nonempty := by
    by_contra hn
    have ht : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    apply hH
    rw [heq, ht, soninFiniteDilationSource, Finset.sum_empty]
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image t (fun q => q.1) hne
  have hstrict : ∀ q ∈ t, q ≠ k → q.1 < k.1 := by
    intro q hq hqk
    exact lt_of_le_of_ne (hmax q hq) (fun h => hqk (Subtype.ext h))
  rw [heq] at hvH
  rw [centralSoninProjection, Submodule.starProjection_apply_eq_zero_iff,
    orthogonal_centralSoninCarrier hb] at hvb
  rw [centralSoninProjection, Submodule.starProjection_apply_eq_zero_iff,
    orthogonal_centralSoninCarrier hc] at hvH
  have hsmall := (soninFiniteDilationSource_mem_forbiddenSum_iff
    t Subtype.val (fun q => q.2) w hk (hw k hk) hstrict hb hc hvb).mp hvH
  obtain ⟨i, hi, hri⟩ := horigin k hk
  have hcrossk : c ≤ k.1 * a := hri ▸ hcross i hi
  have hle : c / k.1 ≤ a := (div_le_iff₀ (zero_lt_one.trans k.2)).mpr
    (by simpa [mul_comm] using hcrossk)
  have hsum : v ∈ centralPhysicalForbidden a ⊔ centralFourierForbidden a :=
    sup_le_sup (centralPhysicalForbidden_mono hle) (centralFourierForbidden_mono hle) hsmall
  rw [centralSoninCarrier_eq_orthogonal_sup] at hva
  exact inner_self_eq_zero.mp ((Submodule.mem_orthogonal _ _).mp hva v hsum)

end RHTower
