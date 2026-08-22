import GaloisForLFunctions.RHTower.SoninBandCodimensionTwo
import GaloisForLFunctions.RHTower.SoninExtendedOrthogonalBand
import GaloisForLFunctions.RHTower.SoninCarrierApertureChain
import GaloisForLFunctions.RHTower.SoninCarrierApertureLimits
import GaloisForLFunctions.HTGeometry.CodimensionTwoOrthogonalSum

/-!
# The extended Sonine chain and Burnol's Proposition 4.6 for `L_a`

Burnol's extended Sonine space `L_a` is the perpendicular complement of the *mean-zero* halves of
the two bands (his second proof of Prop. 4.5).  The mean-zero bands form the same kind of
increasing, transversal, closed-sum pair as the bands themselves, so the lattice identity behind
Proposition 4.6 applies verbatim and gives the density of `⋃_{b>a} L_b` in `L_a`.

## Main results

* `meanZeroBand`, `centralMeanZeroFourier`, `centralSoninExtendedCarrier`
* `iInf_meanZeroBand`, `iInf_centralMeanZeroFourier`
* `topologicalClosure_iSup_centralSoninExtendedCarrier` — **Burnol's Prop. 4.6 for `L_a`**
-/

noncomputable section

open MeasureTheory Set

open scoped InnerProductSpace

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem inner_bandIndicator (a : ℝ) (f : SoninL2) :
    ⟪bandIndicator a, f⟫_ℂ = ∫ x in centralInterval a, (f : ℝ → ℂ) x :=
  MeasureTheory.L2.inner_indicatorConstLp_one _ _ f

/-- On a vector supported in the smaller band the two band pairings agree. -/
theorem inner_bandIndicator_eq_of_mem {a b : ℝ} (hab : a ≤ b) {f : SoninL2}
    (hf : f ∈ centralPhysicalForbidden a) :
    ⟪bandIndicator b, f⟫_ℂ = ⟪bandIndicator a, f⟫_ℂ := by
  rw [inner_bandIndicator, inner_bandIndicator]
  refine MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
    (measurableSet_centralInterval b).nullMeasurableSet ?_ ?_
  · exact Set.Icc_subset_Icc (by linarith) hab
  · have hz := (mem_physicalForbidden_iff _ _ f).1 hf
    filter_upwards [hz] with x hx hmem
    exact hx hmem.2

theorem inner_fourierBandIndicator (a : ℝ) (f : SoninL2) :
    ⟪fourierBandIndicator a, f⟫_ℂ = ⟪bandIndicator a, fourierUnitary f⟫_ℂ := by
  rw [← fourierUnitary.inner_map_map (fourierBandIndicator a) f, fourierBandIndicator,
    LinearIsometryEquiv.apply_symm_apply]

theorem inner_fourierBandIndicator_eq_of_mem {a b : ℝ} (hab : a ≤ b) {f : SoninL2}
    (hf : f ∈ centralFourierForbidden a) :
    ⟪fourierBandIndicator b, f⟫_ℂ = ⟪fourierBandIndicator a, f⟫_ℂ := by
  rw [inner_fourierBandIndicator, inner_fourierBandIndicator]
  refine inner_bandIndicator_eq_of_mem hab ?_
  rw [centralFourierForbidden, mem_fourierForbidden_iff] at hf
  exact hf

/-! ### The mean-zero bands -/

/-- The mean-zero part of the frequency band. -/
def centralMeanZeroFourier (a : ℝ) : Submodule ℂ SoninL2 :=
  centralFourierForbidden a ⊓ (ℂ ∙ fourierBandIndicator a)ᗮ

/-- **Burnol's extended Sonine space `L_a`**, in the full-line model. -/
def centralSoninExtendedCarrier (a : ℝ) : Submodule ℂ SoninL2 :=
  (meanZeroBand a ⊔ centralMeanZeroFourier a)ᗮ

theorem meanZeroBand_le (a : ℝ) :
    meanZeroBand a ≤ centralPhysicalForbidden a := by
  rw [meanZeroBand]
  exact inf_le_left

theorem centralMeanZeroFourier_le (a : ℝ) :
    centralMeanZeroFourier a ≤ centralFourierForbidden a := inf_le_left

theorem meanZeroBand_mono {a b : ℝ} (hab : a ≤ b) :
    meanZeroBand a ≤ meanZeroBand b := by
  intro f hf
  have hf1 : f ∈ centralPhysicalForbidden a := meanZeroBand_le a hf
  refine ⟨centralPhysicalForbidden_mono hab hf1, ?_⟩
  show f ∈ (ℂ ∙ bandIndicator b)ᗮ
  refine Submodule.mem_orthogonal_singleton_iff_inner_right.2 ?_
  rw [inner_bandIndicator_eq_of_mem hab hf1]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 hf.2

theorem centralMeanZeroFourier_mono {a b : ℝ} (hab : a ≤ b) :
    centralMeanZeroFourier a ≤ centralMeanZeroFourier b := by
  intro f hf
  refine ⟨centralFourierForbidden_mono hab hf.1, ?_⟩
  show f ∈ (ℂ ∙ fourierBandIndicator b)ᗮ
  refine Submodule.mem_orthogonal_singleton_iff_inner_right.2 ?_
  rw [inner_fourierBandIndicator_eq_of_mem hab hf.1]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 hf.2

theorem iInf_meanZeroBand (a : ℝ) :
    (⨅ b : {b : ℝ // a < b}, meanZeroBand b.1) = meanZeroBand a := by
  haveI : Nonempty {b : ℝ // a < b} := ⟨⟨a + 1, by linarith⟩⟩
  refine le_antisymm ?_ (le_iInf fun b => meanZeroBand_mono (le_of_lt b.2))
  intro f hf
  rw [Submodule.mem_iInf] at hf
  have hband : f ∈ centralPhysicalForbidden a := by
    have hiI := iInf_centralPhysicalForbidden a
    rw [← hiI, Submodule.mem_iInf]
    exact fun b => meanZeroBand_le b.1 (hf b)
  refine ⟨hband, ?_⟩
  show f ∈ (ℂ ∙ bandIndicator a)ᗮ
  refine Submodule.mem_orthogonal_singleton_iff_inner_right.2 ?_
  obtain ⟨b, hb⟩ : ∃ b : {b : ℝ // a < b}, True := ⟨⟨a + 1, by linarith⟩, trivial⟩
  have hzero := Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hf b).2
  rw [← inner_bandIndicator_eq_of_mem (le_of_lt b.2) hband]
  exact hzero

theorem iInf_centralMeanZeroFourier (a : ℝ) :
    (⨅ b : {b : ℝ // a < b}, centralMeanZeroFourier b.1) = centralMeanZeroFourier a := by
  haveI : Nonempty {b : ℝ // a < b} := ⟨⟨a + 1, by linarith⟩⟩
  refine le_antisymm ?_ (le_iInf fun b => centralMeanZeroFourier_mono (le_of_lt b.2))
  intro f hf
  rw [Submodule.mem_iInf] at hf
  have hband : f ∈ centralFourierForbidden a := by
    have := iInf_centralFourierForbidden a
    rw [← this, Submodule.mem_iInf]
    exact fun b => (hf b).1
  refine ⟨hband, ?_⟩
  show f ∈ (ℂ ∙ fourierBandIndicator a)ᗮ
  refine Submodule.mem_orthogonal_singleton_iff_inner_right.2 ?_
  obtain ⟨b, hb⟩ : ∃ b : {b : ℝ // a < b}, True := ⟨⟨a + 1, by linarith⟩, trivial⟩
  have hzero := Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hf b).2
  rw [← inner_fourierBandIndicator_eq_of_mem (le_of_lt b.2) hband]
  exact hzero

theorem centralMeanZero_inf_eq_bot (a : ℝ) :
    meanZeroBand a ⊓ centralMeanZeroFourier a = ⊥ := by
  refine le_antisymm ?_ bot_le
  refine le_trans (inf_le_inf (meanZeroBand_le a) (centralMeanZeroFourier_le a)) ?_
  have h := physicalForbidden_inf_fourierForbidden_eq_bot a
  simpa [centralPhysicalForbidden, centralFourierForbidden] using h.le

theorem isClosed_meanZeroBand (a : ℝ) :
    IsClosed ((meanZeroBand a : Submodule ℂ SoninL2) : Set SoninL2) := by
  have h1 : IsClosed ((physicalForbidden (centralInterval a)
      (measurableSet_centralInterval a) : Submodule ℂ SoninL2) : Set SoninL2) :=
    isClosed_of_hasOrthogonalProjection _
  have h2 : IsClosed (((ℂ ∙ bandIndicator a)ᗮ : Submodule ℂ SoninL2) : Set SoninL2) :=
    Submodule.isClosed_orthogonal _
  rw [meanZeroBand, Submodule.coe_inf]
  exact h1.inter h2

theorem isClosed_centralMeanZeroFourier (a : ℝ) :
    IsClosed ((centralMeanZeroFourier a : Submodule ℂ SoninL2) : Set SoninL2) := by
  have h1 : IsClosed ((centralFourierForbidden a : Submodule ℂ SoninL2) : Set SoninL2) :=
    isClosed_of_hasOrthogonalProjection _
  have h2 : IsClosed (((ℂ ∙ fourierBandIndicator a)ᗮ : Submodule ℂ SoninL2) : Set SoninL2) :=
    Submodule.isClosed_orthogonal _
  rw [centralMeanZeroFourier, Submodule.coe_inf]
  exact h1.inter h2

theorem isClosed_centralMeanZero_sup {a : ℝ} (ha : 0 < a) :
    IsClosed ((meanZeroBand a ⊔ centralMeanZeroFourier a : Submodule ℂ SoninL2) :
      Set SoninL2) := by
  refine isClosed_sup_of_le_of_inf_eq_bot ?_ (centralMeanZero_inf_eq_bot a)
    (meanZeroBand_le a) (centralMeanZeroFourier_le a)
    (isClosed_of_hasOrthogonalProjection _) (isClosed_of_hasOrthogonalProjection _)
    (isClosed_meanZeroBand a) (isClosed_centralMeanZeroFourier a)
    (isClosed_centralPhysicalForbidden_sup_centralFourierForbidden a ha)
  have h := physicalForbidden_inf_fourierForbidden_eq_bot a
  simpa [centralPhysicalForbidden, centralFourierForbidden] using h

/-- **Burnol's Proposition 4.6 for the extended spaces.** -/
theorem topologicalClosure_iSup_centralSoninExtendedCarrier (a : ℝ) (ha : 0 < a) :
    (⨆ b : {b : ℝ // a < b}, centralSoninExtendedCarrier b.1).topologicalClosure =
      centralSoninExtendedCarrier a := by
  haveI : Nonempty {b : ℝ // a < b} := ⟨⟨a + 1, by linarith⟩⟩
  have hkey := topologicalClosure_iSup_orthogonal_sup_eq
    (A := fun b : {b : ℝ // a < b} => meanZeroBand b.1)
    (B := fun b : {b : ℝ // a < b} => centralMeanZeroFourier b.1)
    (fun i j hij => meanZeroBand_mono hij)
    (fun i j hij => centralMeanZeroFourier_mono hij)
    (fun i => centralMeanZero_inf_eq_bot i.1)
    (fun i => isClosed_centralMeanZero_sup (lt_trans ha i.2))
  rw [iInf_meanZeroBand, iInf_centralMeanZeroFourier] at hkey
  exact hkey

/-! ### The chain ends -/

theorem centralSoninCarrier_le_centralSoninExtendedCarrier (a : ℝ) :
    centralSoninCarrier a ≤ centralSoninExtendedCarrier a := by
  rw [centralSoninCarrier_eq_orthogonal_sup, centralSoninExtendedCarrier]
  exact Submodule.orthogonal_le (sup_le_sup (meanZeroBand_le a) (centralMeanZeroFourier_le a))

/-- **`K = ∪_{a>0} L_a`.**  The extended Sonine spaces of positive aperture have dense union. -/
theorem topologicalClosure_iSup_pos_centralSoninExtendedCarrier :
    (⨆ a : {a : ℝ // (0 : ℝ) < a}, centralSoninExtendedCarrier a.1).topologicalClosure = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← topologicalClosure_iSup_pos_centralSoninCarrier]
  exact Submodule.topologicalClosure_mono
    (iSup_mono fun a => centralSoninCarrier_le_centralSoninExtendedCarrier a.1)

theorem mem_orthogonal_meanZeroBand_of_mem_extended {a : ℝ} {f : SoninL2}
    (hf : f ∈ centralSoninExtendedCarrier a) : f ∈ (meanZeroBand a)ᗮ := by
  rw [centralSoninExtendedCarrier] at hf
  exact Submodule.orthogonal_le le_sup_left hf

/-- **`{0} = ∩_{a>0} L_a`.**  A vector constant on every band, together with its transform,
vanishes. -/
theorem iInf_pos_centralSoninExtendedCarrier :
    (⨅ a : {a : ℝ // (0 : ℝ) < a}, centralSoninExtendedCarrier a.1) = ⊥ := by
  classical
  refine le_antisymm (fun f hf => ?_) bot_le
  rw [Submodule.mem_iInf] at hf
  rw [Submodule.mem_bot]
  have hconst : ∀ n : ℕ, ∃ c : ℂ, ∀ᵐ x ∂(volume : Measure ℝ),
      x ∈ centralInterval ((n : ℝ) + 1) → (f : ℝ → ℂ) x = c := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact (mem_orthogonal_meanZeroBand_iff _ f).1
      (mem_orthogonal_meanZeroBand_of_mem_extended (hf ⟨(n : ℝ) + 1, hpos⟩))
  choose c hc using hconst
  -- the constants all agree with the one on the unit band
  have hunit : (volume : Measure ℝ) (centralInterval (1 : ℝ)) ≠ 0 := by
    rw [centralInterval, Real.volume_Icc]
    norm_num
  haveI : (ae ((volume : Measure ℝ).restrict (centralInterval (1 : ℝ)))).NeBot := by
    refine ae_neBot.2 ?_
    intro hzeroμ
    refine hunit ?_
    have hval := congrArg (fun μ : Measure ℝ => μ (centralInterval (1 : ℝ))) hzeroμ
    simpa [Measure.restrict_apply_self] using hval
  have hzero : ∀ n : ℕ, c n = c 0 := by
    intro n
    have hsub : centralInterval (1 : ℝ) ⊆ centralInterval ((n : ℝ) + 1) := by
      refine Set.Icc_subset_Icc ?_ ?_ <;>
        · have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
    have h1 : ∀ᵐ x ∂((volume : Measure ℝ).restrict (centralInterval (1 : ℝ))),
        (f : ℝ → ℂ) x = c n ∧ (f : ℝ → ℂ) x = c 0 := by
      refine (ae_restrict_iff' (measurableSet_centralInterval 1)).2 ?_
      filter_upwards [hc n, hc 0] with x hxn hx0 hmem
      refine ⟨hxn (hsub hmem), hx0 ?_⟩
      simpa using hmem
    obtain ⟨x, hx1, hx2⟩ := h1.exists
    rw [← hx1, hx2]
  have hall : ∀ᵐ x ∂(volume : Measure ℝ), (f : ℝ → ℂ) x = c 0 := by
    have hstep : ∀ᵐ x ∂(volume : Measure ℝ), ∀ n : ℕ,
        x ∈ centralInterval ((n : ℝ) + 1) → (f : ℝ → ℂ) x = c n := ae_all_iff.2 hc
    filter_upwards [hstep] with x hx
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    have hmem : x ∈ centralInterval ((n : ℝ) + 1) := by
      rw [centralInterval, Set.mem_Icc, ← abs_le]
      linarith
    rw [hx n hmem, hzero n]
  have hmem : MemLp (fun _ : ℝ => c 0) 2 (volume : Measure ℝ) :=
    (Lp.memLp f).ae_eq hall
  have hc0 : c 0 = 0 := by
    rcases (memLp_const_iff (p := (2 : ENNReal)) (by norm_num) (by norm_num)).1 hmem with h | h
    · exact h
    · exact absurd h (by simp)
  refine Lp.ext ?_
  filter_upwards [hall] with x hx
  simp [hx, hc0]


end RHTower

end
