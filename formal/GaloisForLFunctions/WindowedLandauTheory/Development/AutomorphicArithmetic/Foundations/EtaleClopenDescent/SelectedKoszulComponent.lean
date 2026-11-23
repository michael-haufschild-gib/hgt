import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechSubquotientExact
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedCechFiltrationExact

/-! For a Koszul cube with a selected subsequence exact below its
length, the selected top component detects boundaries. It can be
prescribed when its class is annihilated by every remaining weight. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH

variable {k κ E : Type} [Field k] [LinearOrder κ] [Fintype κ] [AddCommGroup E] [Module k E]
  {d : ℕ} {M : Submodule k E} {w : κ → Module.End k E}
  (e : Fin d ↪o κ)
  (hw : ∀ i j, Commute (w i) (w j)) (hM : ∀ i, M ≤ M.comap (w i))
  (hK : ∀ m : ℤ, m < (d : ℤ) →
    (acx (fun _ => M) fun j => w (e j)).Z m ≤ (acx (fun _ => M) fun j => w (e j)).B m)

omit [Fintype κ] in
private theorem card_selectedIndices : (selectedIndices e).card = d := by
  simp [selectedIndices]

omit [Fintype κ] in
/-- The selected boundary values are sums of the images of the
individual selected weights on the lattice. -/
theorem selectedBoundaryValues_eq_iSup :
    selectedBoundaryValues M w e = ⨆ j : Fin d, M.map (w (e j)) := by
  classical
  apply le_antisymm
  · rintro v ⟨z, ⟨y, hy, rfl⟩, he⟩
    change wd (fun j => w (e j)) y Finset.univ = v at he
    rw [← he, wd_apply]
    refine Submodule.sum_mem _ fun j hj => zsmul_mem ?_ _
    have hcard : (((Finset.univ : Finset (Fin d)).erase j).card : ℤ) = (d : ℤ) - 1 := by
      have h := Finset.card_erase_add_one hj
      rw [Finset.card_univ, Fintype.card_fin] at h
      omega
    have hmem : y (Finset.univ.erase j) ∈ M := by
      simpa only [hcard, if_true] using acx_mem_terms_iff.mp hy (Finset.univ.erase j)
    exact le_iSup (fun j => M.map (w (e j))) j (Submodule.mem_map_of_mem hmem)
  · refine iSup_le fun j _ hv => ?_
    obtain ⟨v, hvM, rfl⟩ := hv
    let U : Finset (Fin d) := Finset.univ
    let y : Finset (Fin d) → E := Pi.single (U.erase j) (GlobalTheory.cubeSign U j • v)
    refine ⟨wd (fun i => w (e i)) y, ⟨y, ?_, rfl⟩, ?_⟩
    · refine acx_mem_terms_iff.mpr fun L => ?_
      by_cases he : L = U.erase j
      · subst L
        have h := Finset.card_erase_add_one (Finset.mem_univ j)
        rw [Finset.card_univ, Fintype.card_fin] at h
        have h' : ((U.erase j).card : ℤ) = (d : ℤ) - 1 := by
          change (((Finset.univ : Finset (Fin d)).erase j).card : ℤ) = _
          omega
        simpa only [y, Pi.single_eq_same, h', if_true] using zsmul_mem hvM (GlobalTheory.cubeSign U j)
      · rw [show y L = 0 from Pi.single_eq_of_ne he _]
        exact zero_mem _
    · change wd (fun i => w (e i)) y U = w (e j) v
      rw [wd_apply, Finset.sum_eq_single j]
      · have hsign : GlobalTheory.cubeSign U j * GlobalTheory.cubeSign U j = 1 := by
          simp [GlobalTheory.cubeSign, GaloisForLFunctions.HTGeometry.BorelWeil.cechSign, ← mul_pow]
        rw [show y (U.erase j) = GlobalTheory.cubeSign U j • v from Pi.single_eq_same _ _,
          map_zsmul, smul_smul, hsign, one_smul]
      · intro i hi hij
        have hne : U.erase i ≠ U.erase j := fun h =>
          Finset.notMem_erase j U (h ▸ Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
        rw [show y (U.erase i) = 0 from Pi.single_eq_of_ne hne _, map_zero, smul_zero]
      · exact fun h => False.elim (h (Finset.mem_univ j))

include hw hM hK in
/-- A cocycle in the selected top degree is a boundary if its selected
component is a boundary value in the smaller cube. -/
theorem boundary_of_selected_component {c : Finset κ → E}
    (hc : c ∈ (acx (fun _ => M) w).Z (d : ℤ))
    (hvalue : c (selectedIndices e) ∈ selectedBoundaryValues M w e) :
    c ∈ (acx (fun _ => M) w).B (d : ℤ) := by
  let Q := selectedIndices e
  have hcard : Q.card = d := card_selectedIndices e
  have hd (s : Finset κ) : (s.card : ℤ) ≠ (d : ℤ) → c s = 0 := fun hs =>
    (Submodule.mem_bot k).mp (by simpa only [if_neg hs] using acx_mem_terms_iff.mp hc.1 s)
  have htop (s : Finset κ) : levelPart Q (d : ℤ) c s ∈ selectedBoundaryValues M w e := by
    rw [levelPart]
    split_ifs with hs
    · by_cases hs' : (s.card : ℤ) = (d : ℤ)
      · have he : s ∩ Q = s :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
        have he' : s ∩ Q = Q :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
        have hsQ : s = Q := he.symm.trans he'
        exact hsQ.symm ▸ hvalue
      · rw [hd s hs']
        exact zero_mem _
    · exact zero_mem _
  have hL : Lev Q (· ≤ (d : ℤ)) c := fun s hs =>
    False.elim (hs (by
      have := Finset.card_le_card (Finset.inter_subset_right (s₁ := s) (s₂ := Q))
      omega))
  have hcV : wd (wOn Q w) (levelPart Q (d : ℤ) c) = 0 := by
    rw [wd_on_levelPart]
    apply levelPart_eq_zero
    intro s hs
    have := Finset.card_le_card (Finset.inter_subset_right (s₁ := s) (s₂ := Q))
    omega
  obtain ⟨y, hy, hyl, hdy⟩ := exists_top_primitive_of_selectedBoundaryValues M w e hw hM
    (levelPart_mem Q hc.1) (levelPart_support Q (d : ℤ) c) hcV htop
  refine boundary_of_top_level_boundary
    (acx_isCx (fun _ => M) w hw fun _ i _ => hM i) (qEx_of_subsequence_exact M w e hK)
    hc hL hy hyl fun s hs => ?_
  exact (congrFun hdy s).trans (if_pos hs)

include hw hM hK in
/-- A selected top value extends to a cocycle if every unselected
weight sends it to a boundary value in the selected cube. -/
theorem exists_cocycle_with_selected_component {v : E} (hv : v ∈ M)
    (hann : ∀ i ∉ selectedIndices e, w i v ∈ selectedBoundaryValues M w e) :
    ∃ c ∈ (acx (fun _ => M) w).Z (d : ℤ), c (selectedIndices e) = v := by
  let Q := selectedIndices e
  have hcard : Q.card = d := card_selectedIndices e
  let a : Finset κ → E := Pi.single Q v
  have ha : a ∈ (acx (fun _ => M) w).C (d : ℤ) := by
    refine acx_mem_terms_iff.mpr fun s => ?_
    by_cases hs : s = Q
    · subst s
      simpa [a, hcard] using hv
    · rw [show a s = 0 from Pi.single_eq_of_ne hs _]
      exact zero_mem _
  have haL : Lev Q (· = (d : ℤ)) a := fun s hs =>
    Pi.single_eq_of_ne (fun he => hs (by simp [he, hcard])) _
  have haV : wd (wOn Q w) a = 0 := by
    funext s
    rw [wd_apply, Pi.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ Q
    · have hne : s.erase i ≠ Q := fun he => Finset.notMem_erase i s (he ▸ hi)
      rw [show a (s.erase i) = 0 from Pi.single_eq_of_ne hne _, map_zero, smul_zero]
    · simp only [wOn, if_neg hi, LinearMap.zero_apply, smul_zero]
  let b := wd (wOn Qᶜ w) a
  have hb : b ∈ (acx (fun _ => M) w).C ((d : ℤ) + 1) :=
    wd_on_mem hw (fun _ i _ => hM i) Qᶜ ha
  have hbL : Lev Q (· = (d : ℤ)) b := wd_compl_support w haL
  have hbV : wd (wOn Q w) b = 0 := by
    have h := wd_anticommute (wOn Q w) (wOn Qᶜ w) (wOn_commute hw Q Qᶜ) a
    rwa [haV, map_zero, add_zero] at h
  have hbval (s : Finset κ) : b s ∈ selectedBoundaryValues M w e := by
    change wd (wOn Qᶜ w) a s ∈ _
    rw [wd_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i ∈ Q
    · simp [wOn, hi]
    · rw [wOn, if_pos (Finset.mem_compl.mpr hi)]
      by_cases he : s.erase i = Q
      · rw [he, show a Q = v from Pi.single_eq_same _ _]
        exact zsmul_mem (hann i hi) _
      · rw [show a (s.erase i) = 0 from Pi.single_eq_of_ne he _, map_zero, smul_zero]
        exact zero_mem _
  obtain ⟨y, hy, hyl, hdy⟩ :=
    exists_top_primitive_of_selectedBoundaryValues M w e hw hM hb hbL hbV hbval
  rw [add_sub_cancel_right] at hy
  obtain ⟨c, hc, hclev⟩ := exists_cocycle_of_top_level hw (fun _ i _ => hM i)
    (qEx_of_subsequence_exact M w e hK) ha haV hy hyl hdy
  refine ⟨c, hc, ?_⟩
  have hs : ¬ ((Q ∩ Q).card : ℤ) < (d : ℤ) := by simp [hcard]
  have h := hclev Q hs
  change c Q - a Q = 0 at h
  simpa [a, sub_eq_zero] using h

end GlobalTheory.WH
