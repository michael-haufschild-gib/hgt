import GaloisForLFunctions.ZeroConfigurationGeometry.PurityLeavesOnlyThroughCollision
import GaloisForLFunctions.HTGeometry.MultisetNewtonSolve

/-!
# The curve camera identifies at the genus

The camera of the function-field model. A curve of genus `g` over `𝔽_q` has `g` trace points
`t_j = z_j + z_j⁻¹` (`z_j^{±1}` the normalized Frobenius eigenvalues), the complex roots of its
trace polynomial `Q` (`traceConfig`). The explicit formula reads
`#C(𝔽_{q^m}) = q^m + 1 − q^{m/2} S_m` with `S_m = Σ_j (z_j^m + z_j^{-m}) = Σ_j D_m(t_j)`, `D_m` the
Dickson polynomial (`curveImage`, `curveImage_eq_sum_eigenvalues`). The camera of aperture `k`
records `S_1, …, S_k`: the point counts over `𝔽_{q^m}`, `m ≤ k`.

* **The camera sees exactly the top coefficients** (`curveImage_eq_iff_coeff_eq`). For monic trace
  polynomials `Q, Q'` of degree `g` and `k ≤ g`, the images agree up to order `k` iff `Q` and `Q'`
  agree in all degrees `≥ g − k`. The Dickson sums are a unitriangular change of the power sums
  (`curveImage_eq_powerSum_add`), and Newton's identities a unitriangular change between power
  sums and elementary symmetric functions (`powerSum_eq_iff_esymm_eq`).
* **Identification at the genus** (`eq_of_curveImage_eq`). Aperture `g` identifies the
  configuration: the point counts up to `𝔽_{q^g}` determine the zeta function.
* **Mimicry below the genus, inside purity** (`exists_pure_mimics`). For every `g ≥ 1` two distinct
  pure trace polynomials of degree `g` have the same image up to order `g − 1`: a simple pure
  configuration is stable (`eventually_pure_of_simple`), so its constant coefficient can move.
* **Tilted mimics** (`exists_tilted_mimic`). Every monic trace polynomial of degree `g ≥ 1` has a
  mimic up to order `g − 1` with a trace root at `3`, whose eigenvalues leave the unit circle. Below
  the genus the camera certifies the purity of no configuration; at the genus it certifies purity
  of every pure one (`isPure_of_curveImage_eq`).

The threshold is exact and dimensional: the configuration has `g` degrees of freedom, and the
camera of order `m` fixes the coefficient of degree `g − m`.
-/

open Polynomial Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- The **curve image** of order `m` of a configuration of trace points: `Σ_t D_m(t)`. -/
def curveImage (T : Multiset ℂ) (m : ℕ) : ℂ :=
  (T.map fun t => (dickson 1 (1 : ℂ) m).eval t).sum

/-- The complex trace points of a real trace polynomial, with multiplicity. -/
def traceConfig (Q : ℝ[X]) : Multiset ℂ := (Q.map (algebraMap ℝ ℂ)).roots

/-- **The curve image is an eigenvalue power sum**: if `t = r(t) + r(t)⁻¹` on the configuration,
the image of order `m` is `Σ_t (r(t)^m + r(t)^{-m})`. -/
theorem curveImage_eq_sum_eigenvalues (T : Multiset ℂ) (r : ℂ → ℂ)
    (hr : ∀ t ∈ T, r t ≠ 0 ∧ r t + (r t)⁻¹ = t) (m : ℕ) :
    curveImage T m = (T.map fun t => r t ^ m + (r t)⁻¹ ^ m).sum := by
  rw [curveImage]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun t ht => ?_)
  have h := dickson_one_one_eval_add_inv (r t) (r t)⁻¹ (mul_inv_cancel₀ (hr t ht).1) m
  rwa [(hr t ht).2] at h

/-! ### Dickson sums are unitriangular in the power sums -/

/-- `D_m` has degree at most `m`, and is monic of degree `m` for `m ≥ 1`. -/
theorem dickson_natDegree_le_and_coeff : ∀ m : ℕ,
    (dickson 1 (1 : ℂ) m).natDegree ≤ m ∧ (1 ≤ m → (dickson 1 (1 : ℂ) m).coeff m = 1)
  | 0 => ⟨by rw [dickson_zero]; exact (natDegree_sub_le _ _).trans (by simp),
      fun h => absurd h (by norm_num)⟩
  | 1 => ⟨by simp [dickson_one], fun _ => by simp [dickson_one]⟩
  | m + 2 => by
    obtain ⟨h1, h1c⟩ := dickson_natDegree_le_and_coeff (m + 1)
    obtain ⟨h0, _⟩ := dickson_natDegree_le_and_coeff m
    rw [dickson_add_two]
    refine ⟨(natDegree_sub_le _ _).trans (max_le ?_ ?_), fun _ => ?_⟩
    · exact natDegree_mul_le.trans (by rw [natDegree_X]; omega)
    · exact (natDegree_C_mul_le _ _).trans (by omega)
    · rw [coeff_sub, show m + 2 = (m + 1) + 1 from rfl, coeff_X_mul, h1c (by omega), coeff_C_mul,
        coeff_eq_zero_of_natDegree_lt (by omega)]
      simp

theorem eval_dickson_eq {m : ℕ} (hm : 1 ≤ m) (t : ℂ) :
    (dickson 1 (1 : ℂ) m).eval t =
      t ^ m + ∑ i ∈ range m, (dickson 1 (1 : ℂ) m).coeff i * t ^ i := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le (dickson_natDegree_le_and_coeff m).1), sum_range_succ,
    (dickson_natDegree_le_and_coeff m).2 hm, one_mul, add_comm]

theorem multiset_sum_map_finset_sum (T : Multiset ℂ) (f : ℕ → ℂ → ℂ) (s : Finset ℕ) :
    (T.map fun t => ∑ i ∈ s, f i t).sum = ∑ i ∈ s, (T.map fun t => f i t).sum := by
  induction T using Multiset.induction_on with
  | empty => simp
  | cons a T ih => simp [ih, Finset.sum_add_distrib]

/-- The image of order `m ≥ 1` is the `m`-th power sum plus lower power sums. -/
theorem curveImage_eq_powerSum_add (T : Multiset ℂ) {m : ℕ} (hm : 1 ≤ m) :
    curveImage T m = (T.map fun t => t ^ m).sum +
      ∑ i ∈ range m, (dickson 1 (1 : ℂ) m).coeff i * (T.map fun t => t ^ i).sum := by
  rw [curveImage, Multiset.map_congr rfl fun t _ => eval_dickson_eq hm t, Multiset.sum_map_add,
    multiset_sum_map_finset_sum]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => Multiset.sum_map_mul_left)

/-- Equal cardinalities: the images up to order `k` agree iff the power sums up to `k` agree. -/
theorem curveImage_eq_iff_powerSum_eq {M N : Multiset ℂ}
    (hcard : Multiset.card M = Multiset.card N) (k : ℕ) :
    (∀ m, 1 ≤ m → m ≤ k → curveImage M m = curveImage N m) ↔
      ∀ m, 1 ≤ m → m ≤ k → (M.map fun x => x ^ m).sum = (N.map fun x => x ^ m).sum := by
  have h0 : (M.map fun x => x ^ 0).sum = (N.map fun x => x ^ 0).sum := by
    rw [multiset_powerSum_zero, multiset_powerSum_zero, hcard]
  have hlow : ∀ m, (∀ i, 1 ≤ i → i < m →
      (M.map fun x => x ^ i).sum = (N.map fun x => x ^ i).sum) →
      ∑ i ∈ range m, (dickson 1 (1 : ℂ) m).coeff i * (M.map fun x => x ^ i).sum =
        ∑ i ∈ range m, (dickson 1 (1 : ℂ) m).coeff i * (N.map fun x => x ^ i).sum := by
    intro m h
    refine Finset.sum_congr rfl fun i hi => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [h0]
    · rw [h i hi0 (Finset.mem_range.mp hi)]
  constructor
  · intro h m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm hmk
      have e := h m hm hmk
      rw [curveImage_eq_powerSum_add M hm, curveImage_eq_powerSum_add N hm,
        hlow m fun i hi1 him => ih i him hi1 (by omega)] at e
      exact add_right_cancel e
  · intro h m hm hmk
    rw [curveImage_eq_powerSum_add M hm, curveImage_eq_powerSum_add N hm, h m hm hmk,
      hlow m fun i hi1 him => h i hi1 (by omega)]

/-- **Newton's identities, truncated.** Power sums up to order `k` agree iff the elementary
symmetric functions up to order `k` agree. -/
theorem powerSum_eq_iff_esymm_eq (M N : Multiset ℂ) (k : ℕ) :
    (∀ m, 1 ≤ m → m ≤ k → (M.map fun x => x ^ m).sum = (N.map fun x => x ^ m).sum) ↔
      ∀ j ≤ k, M.esymm j = N.esymm j := by
  constructor
  · intro h j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp [Multiset.esymm]
      · rw [multiset_esymm_eq_of_powerSum M j hj0, multiset_esymm_eq_of_powerSum N j hj0,
          h j hj0 hj]
        congr 2
        refine Finset.sum_congr rfl fun a ha => ?_
        obtain ⟨ha1, ha2⟩ := (Finset.mem_filter.1 ha).2
        have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_filter.1 ha).1
        rw [ih a.1 ha2 (by omega), h a.2 (by omega) (by omega)]
  · intro h m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm hmk
      rw [multiset_newton_general M m hm, multiset_newton_general N m hm, h m hmk]
      congr 1
      refine Finset.sum_congr rfl fun a ha => ?_
      obtain ⟨ha1, ha2⟩ := (Finset.mem_filter.1 ha).2
      have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_filter.1 ha).1
      rw [h a.1 (by omega), ih a.2 (by omega) (by omega) (by omega)]

/-! ### The camera sees the top coefficients -/

theorem card_traceConfig (Q : ℝ[X]) : Multiset.card (traceConfig Q) = Q.natDegree := by
  rw [traceConfig, splits_iff_card_roots.mp (IsAlgClosed.splits _), natDegree_map]

/-- Vieta: the coefficient of degree `i` of a monic trace polynomial is `± e_{g−i}` of its trace
points. -/
theorem coeff_eq_esymm_traceConfig {Q : ℝ[X]} (hQ : Q.Monic) {i : ℕ} (hi : i ≤ Q.natDegree) :
    ((Q.coeff i : ℝ) : ℂ) =
      (-1) ^ (Q.natDegree - i) * (traceConfig Q).esymm (Q.natDegree - i) := by
  have hc := coeff_eq_esymm_roots_of_card (p := Q.map (algebraMap ℝ ℂ))
    (splits_iff_card_roots.mp (IsAlgClosed.splits _)) (k := i) (by rw [natDegree_map]; exact hi)
  rw [coeff_map, (hQ.map _).leadingCoeff, one_mul, natDegree_map] at hc
  exact hc

/-- **The curve camera sees exactly the top coefficients.** For monic trace polynomials of degree
`g` and `k ≤ g`, the images agree up to order `k` iff the polynomials agree in degrees `≥ g − k`. -/
theorem curveImage_eq_iff_coeff_eq {Q Q' : ℝ[X]} (hQ : Q.Monic) (hQ' : Q'.Monic)
    (hdeg : Q.natDegree = Q'.natDegree) {k : ℕ} (hk : k ≤ Q.natDegree) :
    (∀ m, 1 ≤ m → m ≤ k → curveImage (traceConfig Q) m = curveImage (traceConfig Q') m) ↔
      ∀ j, Q.natDegree - k ≤ j → Q.coeff j = Q'.coeff j := by
  have hcard : Multiset.card (traceConfig Q) = Multiset.card (traceConfig Q') := by
    rw [card_traceConfig, card_traceConfig, hdeg]
  rw [curveImage_eq_iff_powerSum_eq hcard, powerSum_eq_iff_esymm_eq]
  constructor
  · intro h j hj
    by_cases hjg : j ≤ Q.natDegree
    · have h1 := coeff_eq_esymm_traceConfig hQ hjg
      have h2 := coeff_eq_esymm_traceConfig hQ' (i := j) (by rw [← hdeg]; exact hjg)
      rw [← hdeg] at h2
      have hc : ((Q.coeff j : ℝ) : ℂ) = ((Q'.coeff j : ℝ) : ℂ) := by
        rw [h1, h2, h (Q.natDegree - j) (by omega)]
      exact_mod_cast hc
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
  · intro h j hj
    have hjg : j ≤ Q.natDegree := hj.trans hk
    have h1 := coeff_eq_esymm_traceConfig hQ (Nat.sub_le Q.natDegree j)
    have h2 := coeff_eq_esymm_traceConfig hQ' (i := Q.natDegree - j)
      (by rw [← hdeg]; exact Nat.sub_le Q.natDegree j)
    rw [← hdeg] at h2
    rw [Nat.sub_sub_self hjg] at h1 h2
    have hc : ((Q.coeff (Q.natDegree - j) : ℝ) : ℂ) = ((Q'.coeff (Q.natDegree - j) : ℝ) : ℂ) := by
      rw [h (Q.natDegree - j) (by omega)]
    rw [h1, h2] at hc
    exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hc

/-- **Identification at the genus.** Monic trace polynomials of degree `g` with the same image up
to order `g` are equal. -/
theorem eq_of_curveImage_eq {Q Q' : ℝ[X]} (hQ : Q.Monic) (hQ' : Q'.Monic)
    (hdeg : Q.natDegree = Q'.natDegree)
    (h : ∀ m, 1 ≤ m → m ≤ Q.natDegree →
      curveImage (traceConfig Q) m = curveImage (traceConfig Q') m) : Q = Q' := by
  ext j
  exact (curveImage_eq_iff_coeff_eq hQ hQ' hdeg le_rfl).mp h j (by omega)

/-- **The camera at the genus certifies purity.** -/
theorem isPure_of_curveImage_eq {Q Q' : ℝ[X]} (hQ : Q.Monic) (hQ' : Q'.Monic)
    (hdeg : Q.natDegree = Q'.natDegree) (hpure : IsPure Q)
    (h : ∀ m, 1 ≤ m → m ≤ Q.natDegree →
      curveImage (traceConfig Q) m = curveImage (traceConfig Q') m) : IsPure Q' :=
  eq_of_curveImage_eq hQ hQ' hdeg h ▸ hpure

/-! ### Mimicry below the genus -/

/-- **Tilted mimics below the genus.** Every monic trace polynomial of degree `g ≥ 1` has a monic
mimic of degree `g` up to order `g − 1` with a trace root at `3`, hence not pure. -/
theorem exists_tilted_mimic {Q : ℝ[X]} (hQ : Q.Monic) (hg : 1 ≤ Q.natDegree) :
    ∃ Q' : ℝ[X], Q'.Monic ∧ Q'.natDegree = Q.natDegree ∧ Q'.IsRoot 3 ∧ ¬ IsPure Q' ∧
      ∀ m, 1 ≤ m → m < Q.natDegree →
        curveImage (traceConfig Q) m = curveImage (traceConfig Q') m := by
  set Q' := Q - C (Q.eval 3) with hQ'
  have hdeg' : Q'.natDegree = Q.natDegree := natDegree_sub_C
  have hmon : Q'.Monic :=
    hQ.sub_of_left (degree_C_le.trans_lt (natDegree_pos_iff_degree_pos.mp (by omega)))
  have hroot : Q'.IsRoot 3 := by simp [hQ']
  refine ⟨Q', hmon, hdeg', hroot, fun hp => ?_, fun m hm hmg => ?_⟩
  · have := hp.2 3 ((mem_roots hmon.ne_zero).mpr hroot)
    norm_num at this
  · refine (curveImage_eq_iff_coeff_eq hQ hmon hdeg'.symm (k := Q.natDegree - 1) (by omega)).mpr
      (fun j hj => ?_) m hm (by omega)
    simp [hQ', coeff_C, show j ≠ 0 by omega]

/-- **Pure mimics below the genus.** For every `g ≥ 1` there are two distinct pure monic trace
polynomials of degree `g` with the same image up to order `g − 1`. -/
theorem exists_pure_mimics {g : ℕ} (hg : 1 ≤ g) :
    ∃ Q Q' : ℝ[X], Q.Monic ∧ Q'.Monic ∧ Q.natDegree = g ∧ Q'.natDegree = g ∧ IsPure Q ∧
      IsPure Q' ∧ Q ≠ Q' ∧
        ∀ m, 1 ≤ m → m < g → curveImage (traceConfig Q) m = curveImage (traceConfig Q') m := by
  classical
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  -- the simple pure configuration `{j/g : j < g}`
  set s : Multiset ℝ := (Multiset.range g).map fun j : ℕ => (j : ℝ) / g with hs
  set Q : ℝ[X] := (s.map fun a => X - C a).prod with hQ
  have hmon : Q.Monic := monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a
  have hcs : Multiset.card s = g := by rw [hs, Multiset.card_map, Multiset.card_range]
  have hdeg : Q.natDegree = g := by rw [hQ, natDegree_multiset_prod_X_sub_C_eq_card, hcs]
  have hroots : Q.roots = s := roots_multiset_prod_X_sub_C s
  have hmem : ∀ x ∈ s, 0 ≤ x ∧ x < 1 := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hx
    exact ⟨by positivity, (div_lt_one hg0).mpr (by exact_mod_cast Multiset.mem_range.mp hj)⟩
  have hnodup : s.Nodup := (Multiset.nodup_range g).map fun i j hij => by
    have : (i : ℝ) = j := by
      have := congrArg (· * (g : ℝ)) hij
      simpa [div_mul_cancel₀ _ hg0.ne'] using this
    exact_mod_cast this
  have hQ0 : Q ≠ 0 := hmon.ne_zero
  have hpure : IsPure Q := ⟨splits_iff_card_roots.mpr (by rw [hroots, hdeg, hcs]), fun x hx => by
    rw [hroots] at hx
    obtain ⟨h0, h1⟩ := hmem x hx
    rw [abs_of_nonneg h0]; linarith⟩
  have hfree : ¬ IsFrobeniusCollision Q := by
    rintro (⟨x, hx, hdx⟩ | h2 | h2)
    · have h1 := (one_lt_rootMultiplicity_iff_isRoot hQ0).mpr ⟨hx, hdx⟩
      rw [← count_roots, hroots] at h1
      have := Multiset.nodup_iff_count_le_one.mp hnodup x
      omega
    · have := hmem 2 (by rw [← hroots]; exact (mem_roots hQ0).mpr h2); linarith [this.2]
    · have := hmem (-2) (by rw [← hroots]; exact (mem_roots hQ0).mpr h2); linarith [this.1]
  -- move the constant coefficient inside purity
  set P : ℝ → ℝ[X] := fun ε => Q + C ε with hP
  have hPdeg : ∀ ε, (P ε).natDegree ≤ g := fun ε => by
    simp only [hP, natDegree_add_C, hdeg, le_rfl]
  have hPcont : ∀ j, Continuous fun ε => (P ε).coeff j := fun j => by
    simp only [hP, coeff_add, coeff_C]
    split_ifs
    · exact continuous_const.add continuous_id
    · exact continuous_const
  have hP0 : P 0 = Q := by simp [hP]
  have hev := eventually_pure_of_simple hPdeg hPcont (t₀ := 0) (by rw [hP0]; exact hpure)
    (by rw [hP0, hdeg]) (by rw [hP0]; exact hfree)
  obtain ⟨ε, hεpure, hε0⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (eventually_mem_nhdsWithin :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioi 0)).exists
  have hmon' : (Q + C ε).Monic :=
    hmon.add_of_left (degree_C_le.trans_lt (natDegree_pos_iff_degree_pos.mp (by omega)))
  have hdeg' : (Q + C ε).natDegree = g := by rw [natDegree_add_C, hdeg]
  refine ⟨Q, Q + C ε, hmon, hmon', hdeg, hdeg', hpure, hεpure, fun h => ?_, fun m hm hmg => ?_⟩
  · have := congrArg (fun p => p.coeff 0) h
    simp only [coeff_add, coeff_C_zero, left_eq_add] at this
    exact (Set.mem_Ioi.mp hε0).ne' this
  · refine (curveImage_eq_iff_coeff_eq hmon hmon' (by rw [hdeg, hdeg']) (k := g - 1)
      (by omega)).mpr (fun j hj => ?_) m hm (by omega)
    simp [coeff_C, show j ≠ 0 by omega]

end GaloisForLFunctions.ZeroConfigurationGeometry
