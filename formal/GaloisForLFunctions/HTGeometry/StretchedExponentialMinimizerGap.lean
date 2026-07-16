import GaloisForLFunctions.HTGeometry.StretchedExponentialConvexConfinement
import GaloisForLFunctions.HTGeometry.PowerSumTorelli
import GaloisForLFunctions.HTGeometry.FiberPermanentIdentity

open Filter Finset

namespace GaloisForLFunctions

noncomputable section

lemma eventually_const_mul_log_lt_abs_stretchedFiniteDifference {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (d : ℕ →₀ ℝ) (j : ℕ)
    (hcancel : ∀ k < j, stretchedMoment d k = 0)
    (hmoment : stretchedMoment d j ≠ 0) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ x : ℝ in atTop,
      C * Real.log x < |stretchedFiniteDifference α d x| := by
  have ho := (log_isLittleO_abs_stretchedFiniteDifference hα0 hα1 d j
    hcancel hmoment).const_mul_left C
  have hdiff : ∀ᶠ x : ℝ in atTop,
      0 < ‖|stretchedFiniteDifference α d x|‖ := by
    have hequiv := stretchedFiniteDifference_isEquivalent hα0 hα1 d j hcancel hmoment
    rcases lt_or_gt_of_ne hmoment with hmneg | hmpos
    · have hleadNeg : ∀ᶠ x : ℝ in atTop,
          stretchedFiniteDifferenceLeading α d j x < 0 := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        simp only [stretchedFiniteDifferenceLeading]
        exact mul_neg_of_neg_of_pos
          (mul_neg_of_neg_of_pos
            (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hmneg (pow_pos hα0 _)) (by positivity))
            (Real.exp_pos _))
          (Real.rpow_pos_of_pos hx _)
      have hneg := hequiv.eventually_neg hleadNeg
      filter_upwards [hneg] with x hx
      simpa [Real.norm_eq_abs] using (abs_pos.mpr hx.ne)
    · have hleadPos : ∀ᶠ x : ℝ in atTop,
          0 < stretchedFiniteDifferenceLeading α d j x := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        simp only [stretchedFiniteDifferenceLeading]
        exact mul_pos
          (mul_pos
            (div_pos (mul_pos hmpos (pow_pos hα0 _)) (by positivity))
            (Real.exp_pos _))
          (Real.rpow_pos_of_pos hx _)
      have hpos := hequiv.eventually_pos hleadPos
      filter_upwards [hpos] with x hx
      simpa [Real.norm_eq_abs] using (abs_pos.mpr hx.ne')
  have hlt := ho.eventuallyLT_norm_of_eventually_pos hdiff
  filter_upwards [hlt, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs,
    abs_of_pos (mul_pos hC (Real.log_pos hx1))] at hx
  exact hx

lemma exists_stretchedMoment_ne_of_key_ne {D : ℕ} (u v : Fin D → ℕ)
    (hkey : key u ≠ key v) :
    ∃ j ≤ D, stretchedMoment (tupleDifference u v) j ≠ 0 := by
  have hmulti : (Finset.univ.val.map fun i => ((u i : ℕ) : ℂ)) ≠
      (Finset.univ.val.map fun i => ((v i : ℕ) : ℂ)) := by
    intro h
    apply hkey
    have hnat : Finset.univ.val.map u = Finset.univ.val.map v := by
      apply Multiset.map_injective (Nat.cast_injective : Function.Injective (Nat.cast : ℕ → ℂ))
      simpa only [Multiset.map_map, Function.comp_apply] using h
    ext a
    rw [key_count_map, key_count_map]
    exact congrArg (Multiset.count a) hnat
  obtain ⟨j, hjD, hj⟩ := exists_powerSum_ne_of_ne
    (fun i => ((u i : ℕ) : ℂ)) (fun i => ((v i : ℕ) : ℂ)) hmulti
  refine ⟨j, hjD, ?_⟩
  rw [stretchedMoment_tupleDifference]
  intro hzero
  apply hj
  rw [sub_eq_zero] at hzero
  have hc : (∑ i, ((u i : ℕ) : ℂ) ^ j) =
      ∑ i, ((v i : ℕ) : ℂ) ^ j := by
    exact_mod_cast hzero
  change (∑ i, ((u i : ℕ) : ℂ) ^ j) = ∑ i, ((v i : ℕ) : ℂ) ^ j
  exact hc

lemma exists_first_stretchedMoment_ne {D : ℕ} (u v : Fin D → ℕ)
    (hkey : key u ≠ key v) :
    ∃ j ≤ D, (∀ k < j, stretchedMoment (tupleDifference u v) k = 0) ∧
      stretchedMoment (tupleDifference u v) j ≠ 0 := by
  let S := (Finset.range (D + 1)).filter fun j =>
    stretchedMoment (tupleDifference u v) j ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨j, hjD, hj⟩ := exists_stretchedMoment_ne_of_key_ne u v hkey
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hj⟩⟩
  let j := S.min' hS
  have hjmem := S.min'_mem hS
  have hjle : j ≤ D := by
    have := (Finset.mem_filter.mp hjmem).1
    rw [Finset.mem_range] at this
    omega
  refine ⟨j, hjle, ?_, (Finset.mem_filter.mp hjmem).2⟩
  intro k hk
  by_contra hne
  have hkS : k ∈ S := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr ((Nat.lt_succ_iff.mpr ((Nat.le_of_lt hk).trans hjle))), hne⟩
  exact (not_lt_of_ge (S.min'_le k hkS)) hk

lemma key_eq_iff_multiset_map_eq {D : ℕ} (u v : Fin D → ℕ) :
    key u = key v ↔ Finset.univ.val.map u = Finset.univ.val.map v := by
  constructor
  · intro h
    apply Multiset.ext.mpr
    intro a
    rw [← key_count_map, ← key_count_map, h]
  · intro h
    ext a
    rw [key_count_map, key_count_map, h]

lemma key_shellOffset_ne {D q K : ℕ} (r s : Fin D → ℕ)
    (hKq : K ≤ q) (hr : tupleInWindow q K r) (hs : tupleInWindow q K s)
    (hkey : key r ≠ key s) :
    key (fun i => (shellOffset r hKq hr i : ℕ)) ≠
      key (fun i => (shellOffset s hKq hs i : ℕ)) := by
  intro hoffkey
  apply hkey
  apply (key_eq_iff_multiset_map_eq r s).2
  have hoff := (key_eq_iff_multiset_map_eq
    (fun i => (shellOffset r hKq hr i : ℕ))
    (fun i => (shellOffset s hKq hs i : ℕ))).1 hoffkey
  have hmapped := congrArg (Multiset.map fun a : ℕ => q - K + a) hoff
  rw [Multiset.map_map, Multiset.map_map] at hmapped
  have hrfun : r = fun i => q - K + (shellOffset r hKq hr i : ℕ) := by
    funext i
    exact (shellOffset_add_base r hKq hr i).symm
  have hsfun : s = fun i => q - K + (shellOffset s hKq hs i : ℕ) := by
    funext i
    exact (shellOffset_add_base s hKq hs i).symm
  rw [hrfun, hsfun]
  exact hmapped

lemma stretchedFiniteDifference_shellOffsets_eq {α : ℝ} {D q K : ℕ}
    (r s : Fin D → ℕ) (hKq : K ≤ q)
    (hr : tupleInWindow q K r) (hs : tupleInWindow q K s) :
    stretchedFiniteDifference α
        (tupleDifference
          (fun i => (shellOffset r hKq hr i : ℕ))
          (fun i => (shellOffset s hKq hs i : ℕ)))
        ((q : ℝ) - K) =
      tupleStretchedValuation α r - tupleStretchedValuation α s := by
  rw [stretchedFiniteDifference_tupleDifference]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    have hi := shellOffset_add_base r hKq hr i
    have hicast : ((q - K + (shellOffset r hKq hr i : ℕ) : ℕ) : ℝ) =
        (r i : ℝ) := by exact_mod_cast hi
    push_cast at hicast
    rw [Nat.cast_sub hKq] at hicast
    exact hicast
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    have hi := shellOffset_add_base s hKq hs i
    have hicast : ((q - K + (shellOffset s hKq hs i : ℕ) : ℕ) : ℝ) =
        (s i : ℝ) := by exact_mod_cast hi
    push_cast at hicast
    rw [Nat.cast_sub hKq] at hicast
    exact hicast

lemma eventually_all_window_pair_gap {α C : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hC : 0 < C) (D K : ℕ) :
    ∀ᶠ q : ℕ in atTop, ∀ r s : Fin D → ℕ,
      tupleInWindow q K r → tupleInWindow q K s → key r ≠ key s →
      C * Real.log ((q : ℝ) - K) <
        |tupleStretchedValuation α r - tupleStretchedValuation α s| := by
  have hall : ∀ᶠ x : ℝ in atTop,
      ∀ u v : Fin D → Fin (2 * K + 1),
        key (fun i => (u i : ℕ)) ≠ key (fun i => (v i : ℕ)) →
        C * Real.log x <
          |stretchedFiniteDifference α
            (tupleDifference (fun i => (u i : ℕ)) (fun i => (v i : ℕ))) x| := by
    rw [Filter.eventually_all]
    intro u
    rw [Filter.eventually_all]
    intro v
    by_cases huv : key (fun i => (u i : ℕ)) ≠ key (fun i => (v i : ℕ))
    · obtain ⟨j, _hjD, hcancel, hmoment⟩ :=
        exists_first_stretchedMoment_ne
          (fun i => (u i : ℕ)) (fun i => (v i : ℕ)) huv
      exact (eventually_const_mul_log_lt_abs_stretchedFiniteDifference
        hα0 hα1 _ j hcancel hmoment hC).mono fun x hx _ => hx
    · exact Filter.Eventually.of_forall fun _ h => (huv h).elim
  have hbase : Tendsto (fun q : ℕ => (q : ℝ) - K) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-(K : ℝ)) tendsto_natCast_atTop_atTop
  filter_upwards [hbase.eventually hall, eventually_ge_atTop K] with q hqgap hKq
  intro r s hr hs hkey
  have hoffkey := key_shellOffset_ne r s hKq hr hs hkey
  have hgap := hqgap
    (shellOffset r hKq hr) (shellOffset s hKq hs) hoffkey
  rwa [stretchedFiniteDifference_shellOffsets_eq r s hKq hr hs] at hgap

lemma boundaryOffsetCandidate_eventually_const_log_gap {α C : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hC : 0 < C)
    {D L : ℕ} (δ : Fin D → ℕ)
    (hLsq : (∑ i, (δ i : ℝ) ^ 2) < (L : ℝ) ^ 2)
    (u : Fin D → Fin (2 * L + 1)) (hu : boundaryOffsetCandidate δ u) :
    ∀ᶠ x : ℝ in atTop, C * Real.log x <
      stretchedFiniteDifference α
        (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) x := by
  have hm0 : stretchedMoment
      (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) 0 = 0 := by
    rw [stretchedMoment_tupleDifference]
    simp
  have hm1nn := boundaryOffsetCandidate_moment_one_nonneg δ u hu
  rcases hm1nn.eq_or_lt with hm1 | hm1
  · have hm2 := boundaryOffsetCandidate_moment_two_pos_of_moment_one_zero δ u hu hLsq hm1.symm
    have hgap := eventually_const_mul_log_lt_abs_stretchedFiniteDifference
      hα0 hα1 _ 2
        (by
          intro k hk
          interval_cases k
          · exact hm0
          · exact hm1.symm)
        hm2.ne' hC
    have hpos := (stretchedFiniteDifference_isEquivalent hα0 hα1 _ 2
      (by
        intro k hk
        interval_cases k
        · exact hm0
        · exact hm1.symm) hm2.ne').eventually_pos (by
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
          simp only [stretchedFiniteDifferenceLeading]
          exact mul_pos
            (mul_pos (div_pos (mul_pos hm2 (pow_pos hα0 _)) (by positivity))
              (Real.exp_pos _))
            (Real.rpow_pos_of_pos hx _))
    filter_upwards [hgap, hpos] with x hgapx hposx
    rwa [abs_of_pos hposx] at hgapx
  · have hgap := eventually_const_mul_log_lt_abs_stretchedFiniteDifference
      hα0 hα1 _ 1 (by intro k hk; interval_cases k; exact hm0) hm1.ne' hC
    have hpos := (stretchedFiniteDifference_isEquivalent hα0 hα1 _ 1
      (by intro k hk; interval_cases k; exact hm0) hm1.ne').eventually_pos (by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        simp only [stretchedFiniteDifferenceLeading]
        exact mul_pos
          (mul_pos (div_pos (mul_pos hm1 (pow_pos hα0 _)) (by positivity))
            (Real.exp_pos _))
          (Real.rpow_pos_of_pos hx _))
    filter_upwards [hgap, hpos] with x hgapx hposx
    rwa [abs_of_pos hposx] at hgapx

lemma boundaryOffsetCandidate_eventually_all_const_log_gap {α C : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hC : 0 < C)
    {D L : ℕ} (δ : Fin D → ℕ)
    (hLsq : (∑ i, (δ i : ℝ) ^ 2) < (L : ℝ) ^ 2) :
    ∀ᶠ x : ℝ in atTop, ∀ u : Fin D → Fin (2 * L + 1),
      boundaryOffsetCandidate δ u → C * Real.log x <
        stretchedFiniteDifference α
          (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) x := by
  rw [Filter.eventually_all]
  intro u
  by_cases hu : boundaryOffsetCandidate δ u
  · exact (boundaryOffsetCandidate_eventually_const_log_gap
      hα0 hα1 hC δ hLsq u hu).mono fun x hx _ => hx
  · exact Filter.Eventually.of_forall fun _ hx => (hu hx).elim

/-- Quantitative version of bounded minimizer confinement.  Besides placing every minimizer in a
fixed window, it separates its distinct multiplicity key from every competitor by any prescribed
constant multiple of the logarithmic scale. -/
theorem exists_eventually_logGap_stretchedMinimizer {α Cgap : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hCgap : 0 < Cgap)
    {D : ℕ} (hD : 0 < D) (δ : Fin D → ℕ) (Csum : ℕ) :
    ∃ K : ℕ, ∀ᶠ q : ℕ in atTop,
      ∀ (A : Finset (Fin D → ℕ)),
        (fun i => q + δ i) ∈ A →
        (∀ s ∈ A,
          D * q + (∑ i, δ i) ≤ ∑ i, s i ∧
          (∑ i, s i) ≤ D * q + (∑ i, δ i) + Csum) →
        ∀ s ∈ A,
          (∀ r ∈ A,
            tupleStretchedValuation α s ≤ tupleStretchedValuation α r) →
          tupleInWindow q K s ∧
          ∀ r ∈ A, key r ≠ key s →
            Cgap * Real.log ((q : ℝ) - (K + 1)) <
              tupleStretchedValuation α r - tupleStretchedValuation α s := by
  classical
  let Aδ := ∑ i, δ i
  let Sδ := ∑ i, (δ i) ^ 2
  let K := Csum + Aδ + Sδ + 1
  let L := K + 1
  have hCtotK : Aδ + Csum < K := by
    dsimp [K]
    omega
  have hLpos : 0 < L := by dsimp [L, K]; omega
  have hSltL : Sδ < L := by dsimp [L, K]; omega
  have hSltLsq : Sδ < L ^ 2 :=
    hSltL.trans_le (by nlinarith : L ≤ L ^ 2)
  have hLsq : (∑ i, (δ i : ℝ) ^ 2) < (L : ℝ) ^ 2 := by
    have hcast : (Sδ : ℝ) < (L : ℝ) ^ 2 := by exact_mod_cast hSltLsq
    simpa [Sδ] using hcast
  obtain ⟨Q, hrecord⟩ := exists_stretchedIncrement_record_strict hα0 hα1
  have hboundaryReal := boundaryOffsetCandidate_eventually_all_const_log_gap
    hα0 hα1 hCgap δ hLsq
  have hbaseL : Tendsto (fun q : ℕ => (q : ℝ) - L) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-(L : ℝ)) tendsto_natCast_atTop_atTop
  have hboundaryNat : ∀ᶠ q : ℕ in atTop,
      ∀ u : Fin D → Fin (2 * L + 1), boundaryOffsetCandidate δ u →
        Cgap * Real.log ((q : ℝ) - L) <
          stretchedFiniteDifference α
            (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L))
            ((q : ℝ) - L) := hbaseL.eventually hboundaryReal
  have hwindow := eventually_all_window_pair_gap hα0 hα1 hCgap D K
  refine ⟨K, ?_⟩
  filter_upwards [hboundaryNat, hwindow,
    eventually_ge_atTop (max (L + 2) (Q + 1))] with q hboundary hwindowgap hq
  intro A hwitness hbounds s hs hmin
  have hLq : L ≤ q := by omega
  have hKq : K ≤ q := by dsimp [L] at hLq; omega
  have hqQ : Q + 1 ≤ q := by omega
  have hsBounds := hbounds s hs
  have hsumLower0 : D * q ≤ ∑ i, s i :=
    (Nat.le_add_right _ Aδ).trans (by simpa [Aδ] using hsBounds.1)
  have hsumUpper0 : (∑ i, s i) ≤ D * q + (Aδ + Csum) := by
    simpa [Aδ, Nat.add_assoc] using hsBounds.2
  have hswide : tupleInWindow q K s := by
    by_contra hsout
    obtain ⟨t, htsum, htwide, htout, htval⟩ :=
      exists_boundaryShell_of_sum_bounds hD hCtotK hqQ hrecord s
        hsumLower0 hsumUpper0 hsout
    have htsumLower : D * q + (∑ i, δ i) ≤ ∑ i, t i := by
      rw [htsum]
      exact hsBounds.1
    have hcand := shellOffset_boundaryCandidate δ t hLq htwide htout htsumLower
    have hgap := hboundary (shellOffset t hLq htwide) hcand
    rw [stretchedFiniteDifference_shellOffset_eq δ t hLq htwide] at hgap
    have hminW := hmin (fun i => q + δ i) hwitness
    have hlogPos : 0 < Cgap * Real.log ((q : ℝ) - L) := by
      exact mul_pos hCgap (Real.log_pos (by norm_cast; omega))
    linarith
  refine ⟨hswide, ?_⟩
  intro r hr hkey
  by_cases hrwide : tupleInWindow q K r
  · have hgap := hwindowgap r s hrwide hswide hkey
    have hminr := hmin r hr
    rw [abs_of_nonneg (sub_nonneg.mpr hminr)] at hgap
    have hbaseLpos : 0 < (q : ℝ) - L := by norm_cast; omega
    have hbaseKpos : 0 < (q : ℝ) - K := by norm_cast; omega
    have hlogle : Real.log ((q : ℝ) - L) ≤ Real.log ((q : ℝ) - K) := by
      rw [Real.log_le_log_iff hbaseLpos hbaseKpos]
      have hKL : (K : ℝ) ≤ (L : ℝ) := by
        exact_mod_cast (show K ≤ L by dsimp [L]; omega)
      linarith
    have hmul := mul_le_mul_of_nonneg_left hlogle hCgap.le
    simpa [L, Nat.cast_add] using hmul.trans_lt hgap
  · have hrBounds := hbounds r hr
    have hrsumLower0 : D * q ≤ ∑ i, r i :=
      (Nat.le_add_right _ Aδ).trans (by simpa [Aδ] using hrBounds.1)
    have hrsumUpper0 : (∑ i, r i) ≤ D * q + (Aδ + Csum) := by
      simpa [Aδ, Nat.add_assoc] using hrBounds.2
    obtain ⟨t, htsum, htwide, htout, htval⟩ :=
      exists_boundaryShell_of_sum_bounds hD hCtotK hqQ hrecord r
        hrsumLower0 hrsumUpper0 hrwide
    have htsumLower : D * q + (∑ i, δ i) ≤ ∑ i, t i := by
      rw [htsum]
      exact hrBounds.1
    have hcand := shellOffset_boundaryCandidate δ t hLq htwide htout htsumLower
    have hgap := hboundary (shellOffset t hLq htwide) hcand
    rw [stretchedFiniteDifference_shellOffset_eq δ t hLq htwide] at hgap
    have hminW := hmin (fun i => q + δ i) hwitness
    have hfinal : Cgap * Real.log ((q : ℝ) - L) <
        tupleStretchedValuation α r - tupleStretchedValuation α s := by
      linarith
    simpa [L, Nat.cast_add] using hfinal

end

end GaloisForLFunctions
