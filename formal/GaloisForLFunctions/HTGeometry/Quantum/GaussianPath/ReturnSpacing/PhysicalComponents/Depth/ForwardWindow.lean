import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.CrossingRecords
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit
import GaloisForLFunctions.HTGeometry.SeparatedPointCount

/-! # Forward waiting for a deeper scalar return from an ordinary entry -/
open Set Filter MeasureTheory Real Topology
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
open SharpOccupation EmptyVisitFlux
noncomputable section

/-- Entries followed by any target point within the prescribed horizon. -/
def followed (A : Finset ℝ) (F : Set ℝ) (W : ℝ) : Finset ℝ := by
  classical
  exact A.filter (fun u => ∃ w ∈ Icc u (u+W), w∈F)

private theorem pack {L W : ℝ} (hL : 0<L) (hW : 0≤W)
    (A B : Finset ℝ) (F : Set ℝ)
    (hs : ∀ x∈A, ∀ y∈A, x≠y → L≤|x-y|)
    (h : ∀ u∈followed A F W, ∃ v∈B, v∈Icc u (u+W)) :
    ((followed A F W).card:ℝ) ≤ (W/L+1)*(B.card:ℝ) := by
  classical
  let S (v : ℝ) := A.filter (fun u => u∈Icc (v-W) v)
  have cover : followed A F W ⊆ B.biUnion S := by
    intro u hu
    obtain ⟨v,hv,hi⟩ := h u hu
    exact Finset.mem_biUnion.mpr ⟨v,hv,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,
      (show u∈Icc (v-W) v from ⟨by linarith only [hi.2],hi.1⟩)⟩⟩
  have bound (v : ℝ) : ((S v).card:ℝ)≤W/L+1 := by
    have hb := card_le_of_separated_of_subset_Icc hL (sub_le_self v hW) (S v)
      (fun x hx y hy => hs x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1)
      (fun _ hx => (Finset.mem_filter.mp hx).2)
    rwa [sub_sub_cancel] at hb
  calc
    _ ≤ ∑ v∈B, ((S v).card:ℝ) := by exact_mod_cast (Finset.card_le_card cover).trans Finset.card_biUnion_le
    _ ≤ ∑ _v∈B, (W/L+1) := Finset.sum_le_sum fun v _ => bound v
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,mul_comm]

private theorem shift_rate (B : ℝ → ℕ) (a W p : ℝ)
    (hB : Tendsto (fun T => (B T:ℝ)/(T-a)) atTop (𝓝 p)) :
    Tendsto (fun T => (B (T+W):ℝ)/(T-a)) atTop (𝓝 p) := by
  have ht : Tendsto (fun T : ℝ => T-a) atTop atTop := by
    simpa only [id_eq,sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-a) tendsto_id
  have h := (hB.comp (tendsto_atTop_add_const_right atTop W tendsto_id)).mul ((ht.const_div_atTop W).const_add 1)
  rw [add_zero,mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (max a (a-W))] with T hT
  have h1 := (le_max_left a (a-W)).trans_lt hT
  have h2 := (le_max_right a (a-W)).trans_lt hT
  change (B (T+W):ℝ)/(T+W-a)*(1+W/(T-a))=_
  field_simp [(sub_pos.mpr h1).ne',(show 0<T+W-a by linarith only [h2]).ne']
  ring

/-- Among actual entries at the outer tolerance, the fraction followed
within W time units by any inner visit is bounded using the true entry
gap and the ratio of the two spectral fluxes. -/
theorem gaussian_deeper_forward_wait :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let E := fun i => -H.2.isHermitian.eigenvalues i
      let L := (N:ℝ)^((48:ℝ)⁻¹)/4
      ∃ σ>0, orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        ∀ ε∈Ioc (0:ℝ) (1/10), ∀ δ∈Ioc (0:ℝ) ε, ∀ W : ℝ, 0≤W →
          let A := entriesAfter E (physicalArc ε) σ
          ∀ b : ℝ, (W/L+1)*(physicalArc δ/physicalArc ε)^(2^N-2:ℕ)<b →
            ∀ᶠ T : ℝ in atTop, ((followed (A T) (visitSet H 0 δ) W).card:ℝ)/(A T).card < b := by
  classical
  filter_upwards [gaussian_physical_entry_gap,gaussian_first_crossing_flux,gaussian_empty_visit_flux] with ω hg hc hp
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hg,hc] with k hg hc
  intro N H P E L
  obtain ⟨σ,hσ,hfirst,hbefore,hf⟩ := hc
  refine ⟨σ,hσ,hfirst,hbefore,?_⟩
  intro ε hε δ hδ W hW A b hb
  let F := visitSet H 0 δ
  let B := entriesAfter E (physicalArc δ) σ
  have hs : ε<sqrt 2 := hε.2.trans_lt (by nlinarith only [sq_sqrt (show (0:ℝ)≤2 by norm_num),sqrt_nonneg 2])
  have hL : 0<L := by dsimp only [L,N]; positivity
  obtain ⟨hA,ha⟩ := hf ε hε.1 hs
  obtain ⟨hB,hb'⟩ := hf δ hδ.1 (hδ.2.trans_lt hs)
  have hpos := (hp k ε hε.1 hs).2.1
  have hne : pairTurnRate E≠0 := (mul_ne_zero_iff.mp hpos.ne').2
  have ht := ((shift_rate (fun T => (B T).card) σ W _ hb').div ha hpos.ne').const_mul (W/L+1)
  rw [mul_div_mul_right _ _ hne,←div_pow] at ht
  filter_upwards [ht.eventually_lt_const hb,eventually_gt_atTop σ] with T hT hσT
  have sub : F ⊆ visitSet H 0 ε := by
    rintro z ⟨p,hp',C,hC,h⟩
    exact ⟨p,hp',C,hC,h.trans hδ.2⟩
  have strict (u v : ℝ) (hu : u∈A T) (hv : v∈A T) (hlt : u<v) : L<v-u :=
    hg ε hε u ((hA ..).mp hu).2.2.1 v ((hA ..).mp hv).2.2.1 hlt ((hA ..).mp hv).2.2.2
  have hpack := pack hL hW (A T) (B (T+W)) F (fun x hx y hy hxy => by
    rcases lt_or_gt_of_ne hxy with h|h
    · rw [abs_of_neg (sub_neg.mpr h),neg_sub]
      exact (strict x y hx hy h).le
    · rw [abs_of_pos (sub_pos.mpr h)]
      exact (strict y x hy hx h).le) (fun u hu => by
      obtain ⟨hu',w,hw,hf'⟩ := Finset.mem_filter.mp hu
      obtain ⟨hau,huT,_,hd⟩ := (hA ..).mp hu'
      by_cases huF : u∈F
      · obtain ⟨d,hd,hn⟩ := hd
        exact ⟨u,(hB ..).mpr ⟨hau,huT.trans (le_add_of_nonneg_right hW),huF,d,hd,
          fun z hz hzF => hn z hz (sub hzF)⟩,le_rfl,le_add_of_nonneg_right hW⟩
      · let v := PrecisionReturns.firstVisit H u 0 δ
        have hv := PrecisionReturns.firstVisit_isLeast H u 0 hδ.1
        have huv : u<v := lt_of_le_of_ne hv.1.1 (fun he => huF (he ▸ hv.1.2))
        have hvw : v≤w := hv.2 ⟨hw.1,hf'⟩
        have hi : v∈Icc u (u+W) := ⟨huv.le,hvw.trans hw.2⟩
        apply Exists.intro v
        refine ⟨(hB ..).mpr ⟨hau.trans huv,hi.2.trans (add_le_add huT le_rfl),hv.1.2,v-u,sub_pos.mpr huv,?_⟩,hi⟩
        intro z hz hzF
        exact hz.2.not_ge (hv.2 ⟨by linarith only [hz.1],hzF⟩))
  have he := div_div_div_cancel_right₀ (sub_pos.mpr hσT).ne' ((B (T+W)).card:ℝ) ((A T).card:ℝ)
  change (W/L+1)*(((B (T+W)).card:ℝ)/(T-σ)/(((A T).card:ℝ)/(T-σ)))<b at hT
  rw [he,←mul_div_assoc] at hT
  exact (div_le_div_of_nonneg_right hpack (Nat.cast_nonneg _)).trans_lt hT

#print axioms gaussian_deeper_forward_wait
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
