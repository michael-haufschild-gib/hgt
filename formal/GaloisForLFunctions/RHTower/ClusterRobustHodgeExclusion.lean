import GaloisForLFunctions.RHTower.LowHeightHodgeExclusion
import GaloisForLFunctions.RHTower.ZeroLatticeDepthNyquistLaw

/-!
# Cluster-robust Hodge exclusion and its Nyquist sharpness

Let `Z` be a zero configuration with local count `N(t, t+1] ≤ A₀ log(|t| + 3)` and let `ρ₀` be a
zero with `|β₀ - ½| ≥ δ > 0` at height `|γ₀| ≥ 2`.  Let `n` be the number of distinct zeros with
`|γ - γ₀| ≤ 101`.  The level-`a` Hodge index (Weil positivity on `C²` tests supported in
`[-a, a]` whose transforms vanish at `±i/2`) fails as soon as

> `a ≥ max(e⁶, 1/δ)` and `100((n + 1) log² a + log(A₀(|γ₀| + 4))) ≤ a`

(`not_hodgeIndex_below_cluster_horizon`).  For `ζ` the window count is `O(log |γ₀|)`, so the
level-`a` Hodge index excludes zeros of depth `δ` up to height `exp(a/(10⁵ A₀ log² a))`
(`zeta_hodge_index_cluster_horizon`).

The test is the root-killing convolution of `LowHeightHodgeExclusion`, with two changes.

* The centre is a zero `ρ₁` near `ρ₀`, chosen by repeated halving
  (`exists_empty_annulus_center`, `cluster_selection`): a ball holding `m` points either has an
  empty annulus of ratio `λ` or contains two disjoint half-balls, one of which holds at most
  `m/2` points.  After `⌊log₂ n⌋ + 1` steps the killing distance is `ε₀/(2(4λ)^{⌊log₂ n⌋+1})`,
  instead of the `ε₀/λ^n` given by pigeonhole over `n + 1` scales.
* The polar root enters the tail estimate with power `4` instead of `4n + 8`
  (`norm_sq_lowHeightProfile_tail_split`).

The dependence on `n` is linear up to the factor `log² a`, and a linear dependence is necessary:
the off-line lattice `{½ ± δ + 2πik/L}` has local count `O(L)`, at most `1000 L` zeros in every
window of half-width `101`, zeros of depth `δ` above every height, and it satisfies the Hodge index
at every level `a ≤ L/2` (`offLineLattice_masks_at_linear_level`).  Hence no criterion of the form
"`n ≤ 2000 a` forces a violation" holds (`not_forall_hodge_exclusion_sublinear_level`).
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23


/-! ### Empty annulus by halving -/

/-- **Empty annulus by halving.**  Let `P` be a finite set of points, `p ∈ P`, `r > 0`, `λ ≥ 1`,
and suppose the ball `‖q - p‖ < r` contains at most `2^k` points of `P`.  Then some `c ∈ P` and
`t ≥ r/(4λ)^k` satisfy `‖c - p‖ + t ≤ r`, and no point of `P` lies in the annulus
`t/(2λ) ≤ ‖q - c‖ < t/2`.

If the annulus around `p` of radii `r/(2λ)`, `r/2` is occupied by some `q`, the disjoint balls of
radius `‖q - p‖/2` around `p` and `q` lie in the ball of radius `r`, so one of them carries at most
half of its points, and the argument recurses there. -/
theorem exists_empty_annulus_center (P : Finset ℂ) {lam : ℝ} (hlam : 1 ≤ lam) :
    ∀ (k : ℕ) (p : ℂ) (r : ℝ), p ∈ P → 0 < r →
      (P.filter fun q => ‖q - p‖ < r).card ≤ 2 ^ k →
      ∃ c ∈ P, ∃ t : ℝ, r / (4 * lam) ^ k ≤ t ∧ t ≤ r ∧ ‖c - p‖ + t ≤ r ∧
        ∀ q ∈ P, ‖q - c‖ < t / 2 → ‖q - c‖ < t / (2 * lam) := by
  classical
  have hlam0 : 0 < lam := by linarith
  intro k
  induction k with
  | zero =>
    intro p r hp hr hcard
    refine ⟨p, hp, r, by simp, le_rfl, by simp, fun q hq hqc => ?_⟩
    have hmem : q ∈ P.filter (fun q => ‖q - p‖ < r) :=
      Finset.mem_filter.mpr ⟨hq, by linarith⟩
    have hpmem : p ∈ P.filter (fun q => ‖q - p‖ < r) :=
      Finset.mem_filter.mpr ⟨hp, by simp [hr]⟩
    rw [pow_zero] at hcard
    have := Finset.card_le_one.mp hcard q hmem p hpmem
    subst this
    simp only [sub_self, norm_zero]
    positivity
  | succ k ih =>
    intro p r hp hr hcard
    by_cases hA : ∀ q ∈ P, ‖q - p‖ < r / 2 → ‖q - p‖ < r / (2 * lam)
    · refine ⟨p, hp, r, ?_, le_rfl, by simp, hA⟩
      exact div_le_self hr.le (one_le_pow₀ (by linarith))
    push Not at hA
    obtain ⟨q, hq, hq1, hq2⟩ := hA
    set d := ‖q - p‖ with hd
    have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hq2
    set Fp := P.filter fun x => ‖x - p‖ < d / 2 with hFp
    set Fq := P.filter fun x => ‖x - q‖ < d / 2 with hFq
    have hdisj : Disjoint Fp Fq := by
      rw [Finset.disjoint_left]
      intro x hxp hxq
      have h1 := (Finset.mem_filter.mp hxp).2
      have h2 := (Finset.mem_filter.mp hxq).2
      have : d ≤ ‖x - p‖ + ‖x - q‖ := by
        calc d = ‖(x - p) - (x - q)‖ := by rw [hd]; congr 1; ring
          _ ≤ ‖x - p‖ + ‖x - q‖ := norm_sub_le _ _
      linarith
    have hsub : Fp ∪ Fq ⊆ P.filter fun x => ‖x - p‖ < r := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨hxP, hx'⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨hxP, by linarith⟩
      · obtain ⟨hxP, hx'⟩ := Finset.mem_filter.mp hx
        refine Finset.mem_filter.mpr ⟨hxP, ?_⟩
        calc ‖x - p‖ = ‖(x - q) + (q - p)‖ := by congr 1; ring
          _ ≤ ‖x - q‖ + d := norm_add_le _ _
          _ < r := by linarith
    have hsum : Fp.card + Fq.card ≤ 2 ^ (k + 1) := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact (Finset.card_le_card hsub).trans hcard
    have hr' : r / (4 * lam) ≤ d / 2 := by
      have e : r / (4 * lam) = r / (2 * lam) / 2 := by field_simp; ring
      rw [e]; linarith
    have key : ∀ c₀ ∈ P, ‖c₀ - p‖ ≤ d →
        (P.filter fun x => ‖x - c₀‖ < d / 2).card ≤ 2 ^ k →
        ∃ c ∈ P, ∃ t : ℝ, r / (4 * lam) ^ (k + 1) ≤ t ∧ t ≤ r ∧ ‖c - p‖ + t ≤ r ∧
          ∀ q ∈ P, ‖q - c‖ < t / 2 → ‖q - c‖ < t / (2 * lam) := by
      intro c₀ hc₀ hc₀p hcard'
      obtain ⟨c, hc, t, ht1, ht2, ht3, ht4⟩ := ih c₀ (d / 2) hc₀ (by positivity) hcard'
      refine ⟨c, hc, t, ?_, by linarith, ?_, ht4⟩
      · calc r / (4 * lam) ^ (k + 1) = r / (4 * lam) / (4 * lam) ^ k := by
              rw [pow_succ]; field_simp
          _ ≤ d / 2 / (4 * lam) ^ k := by gcongr
          _ ≤ t := ht1
      · have := norm_sub_le_norm_sub_add_norm_sub c c₀ p
        linarith
    rcases le_or_gt Fp.card (2 ^ k) with h | h
    · exact key p hp (by simp; positivity) h
    · have : Fq.card ≤ 2 ^ k := by rw [pow_succ] at hsum; omega
      exact key q hq le_rfl this


/-! ### The split tail bound -/

/-- `(e^{1/2}·168)^{2N₀}(H + 1)^{4n+4}(G + 1)⁴`, the tail constant of the low-height profile when
the killed and phase roots lie within `H` of the centre and the polar root at distance `G`. -/
def clusterTailConstant (H G : ℝ) (N₀ n : ℕ) : ℝ :=
  (Real.exp (1 / 2) * 168) ^ (2 * N₀) * (H + 1) ^ (4 * n + 4) * (G + 1) ^ 4

/-- Tail estimate with separate distance bounds for the killed roots, the polar pair and the
phase pair. -/
theorem norm_sq_lowHeightProfile_tail_split {k : ℕ} {K : List ℂ} {p c x : ℂ} {H G : ℝ}
    (hH : 0 ≤ H) (hG : 0 ≤ G) (hx : |x.im| ≤ 1 / 2)
    (hK : ∀ r ∈ pairRoots K, ‖x - r‖ ≤ (H + 1) * (1 + |x.re|))
    (hp : ‖x - p‖ ≤ (G + 1) * (1 + |x.re|)) (hp' : ‖x - conj p‖ ≤ (G + 1) * (1 + |x.re|))
    (hc : ‖x - c‖ ≤ (H + 1) * (1 + |x.re|)) (hc' : ‖x - conj c‖ ≤ (H + 1) * (1 + |x.re|))
    {N₀ n E : ℕ} (hN : k + 2 * (K ++ [p, c]).length + 1 = N₀) (hKn : K.length ≤ n)
    (hE : E + 3 + 4 * (n + 2) ≤ 4 * N₀) :
    ‖lowHeightProfile (sinhTestWeight 1) k (K ++ [p, c]) x‖ ^ 2 * (1 + |x.re|) ^ (3 + E) ≤
      clusterTailConstant H G N₀ n := by
  set D := 1 + |x.re| with hD
  have hD1 : 1 ≤ D := by linarith [abs_nonneg x.re]
  have hD0 : 0 < D := by linarith
  have hW : ContDiff ℝ 2 (fun u => (sinhTestWeight 1 u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (sinhTestWeight_contDiff 1)
  have hWs : ∀ u, (fun u => (sinhTestWeight 1 u : ℂ)) u ≠ 0 → |u| ≤ 1 := fun u hu =>
    sinhTestWeight_supp zero_le_one u (fun h => hu (by simp [h]))
  have hdec := norm_paperFT_le_decay hW hWs x
  change _ ≤ Real.exp _ * (4 * testNorm (sinhTestWeight 1)) / _ at hdec
  set B := Real.exp (1 / 2) * 168 with hB
  have hB0 : 0 ≤ B := by positivity
  have hwx : ‖paperFT (fun u => (sinhTestWeight 1 u : ℂ)) x‖ * D ^ 2 ≤ B := by
    have hN := testNorm_unitWeight_le
    have hN0 := testNorm_nonneg (sinhTestWeight 1)
    have h1 : ‖paperFT (fun u => (sinhTestWeight 1 u : ℂ)) x‖ * D ^ 2 ≤
        Real.exp (1 / 2) * (4 * testNorm (sinhTestWeight 1)) := by
      rw [← le_div_iff₀ (by positivity)]
      refine hdec.trans ?_
      gcongr
      linarith
    refine h1.trans ?_
    rw [hB]; gcongr; linarith
  have hHD : 0 ≤ (H + 1) * D := by positivity
  have hKprod := norm_list_prod_le_pow hHD (fun r => x - r) hK
  rw [pairRoots_length] at hKprod
  set m := K.length with hm
  have h4 : ‖([p, conj p, c, conj c].map fun r => x - r).prod‖ ≤
      ((G + 1) * D) ^ 2 * ((H + 1) * D) ^ 2 := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, norm_mul]
    have e1 : ‖x - p‖ * ‖x - conj p‖ ≤ ((G + 1) * D) ^ 2 := by
      rw [sq]; exact mul_le_mul hp hp' (norm_nonneg _) (by positivity)
    have e2 : ‖x - c‖ * ‖x - conj c‖ ≤ ((H + 1) * D) ^ 2 := by
      rw [sq]; exact mul_le_mul hc hc' (norm_nonneg _) hHD
    calc ‖x - p‖ * (‖x - conj p‖ * (‖x - c‖ * ‖x - conj c‖))
        = (‖x - p‖ * ‖x - conj p‖) * (‖x - c‖ * ‖x - conj c‖) := by ring
      _ ≤ ((G + 1) * D) ^ 2 * ((H + 1) * D) ^ 2 :=
          mul_le_mul e1 e2 (by positivity) (by positivity)
  rw [lowHeightProfile_eq_pairRoots, pairRoots_append, pairRoots_pc, List.map_append,
    List.prod_append, norm_mul, norm_mul, norm_pow, hN]
  set a := ‖paperFT (fun u => (sinhTestWeight 1 u : ℂ)) x‖ with ha
  set P1 := ‖((pairRoots K).map fun r => x - r).prod‖ with hP1
  set P2 := ‖([p, conj p, c, conj c].map fun r => x - r).prod‖ with hP2
  have ha0 : 0 ≤ a := norm_nonneg _
  have hP10 : 0 ≤ P1 := norm_nonneg _
  have hP20 : 0 ≤ P2 := norm_nonneg _
  have hlen : (K ++ [p, c]).length = m + 2 := by simp [hm]
  rw [hlen] at hN
  set e := 2 * N₀ - (2 * m + 4) with he
  have hsplit : D ^ (2 * N₀) = D ^ (2 * m + 4) * D ^ e := by rw [← pow_add]; congr 1; omega
  have hmain : a ^ N₀ * (P1 * P2) * D ^ (2 * m + 4) * D ^ e ≤
      B ^ N₀ * (H + 1) ^ (2 * m + 2) * (G + 1) ^ 2 * D ^ (2 * m + 4) := by
    calc a ^ N₀ * (P1 * P2) * D ^ (2 * m + 4) * D ^ e = (a * D ^ 2) ^ N₀ * P1 * P2 := by
          rw [mul_pow, ← pow_mul, hsplit]; ring
      _ ≤ B ^ N₀ * ((H + 1) * D) ^ (2 * m) * (((G + 1) * D) ^ 2 * ((H + 1) * D) ^ 2) := by
          gcongr
      _ = _ := by simp only [mul_pow]; ring
  have hX : a ^ N₀ * (P1 * P2) * D ^ e ≤ B ^ N₀ * (H + 1) ^ (2 * m + 2) * (G + 1) ^ 2 := by
    have hDp : 0 < D ^ (2 * m + 4) := by positivity
    have : a ^ N₀ * (P1 * P2) * D ^ e * D ^ (2 * m + 4) ≤
        B ^ N₀ * (H + 1) ^ (2 * m + 2) * (G + 1) ^ 2 * D ^ (2 * m + 4) := by
      calc _ = a ^ N₀ * (P1 * P2) * D ^ (2 * m + 4) * D ^ e := by ring
        _ ≤ _ := hmain
    exact le_of_mul_le_mul_right this hDp
  have hX2 := pow_le_pow_left₀ (by positivity) hX 2
  have hEe : 3 + E ≤ 2 * e := by omega
  have hH1 : (1 : ℝ) ≤ H + 1 := by linarith
  calc (a ^ N₀ * (P1 * P2)) ^ 2 * D ^ (3 + E) ≤ (a ^ N₀ * (P1 * P2)) ^ 2 * D ^ (2 * e) := by
        gcongr
    _ = (a ^ N₀ * (P1 * P2) * D ^ e) ^ 2 := by ring
    _ ≤ (B ^ N₀ * (H + 1) ^ (2 * m + 2) * (G + 1) ^ 2) ^ 2 := hX2
    _ = B ^ (2 * N₀) * (H + 1) ^ (4 * m + 4) * (G + 1) ^ 4 := by ring
    _ ≤ B ^ (2 * N₀) * (H + 1) ^ (4 * n + 4) * (G + 1) ^ 4 := by
        gcongr
    _ = clusterTailConstant H G N₀ n := rfl

/-- The tail bound for the roots of the low-height test, with the polar root counted separately. -/
theorem lowHeight_tail_bound_split {γ₀ c δ H : ℝ} {Kset : Finset ℂ} (Z : ZeroConfig)
    (hH : 1 / 2 ≤ H) (hcδ : c ∈ Icc (-δ) δ) (hδ2 : δ ≤ 1 / 2)
    (hK : ∀ ρ ∈ Kset, ρ ∈ Z.carrier ∧ |ρ.im - γ₀| ≤ H) {k N₀ n E : ℕ}
    (hk : k + 2 * (lowHeightRoots γ₀ c Kset).length + 1 = N₀) (hKn : Kset.card ≤ n)
    (hE : E + 3 + 4 * (n + 2) ≤ 4 * N₀) (x : ℂ) (hx : |x.im| ≤ 1 / 2) :
    ‖lowHeightProfile (sinhTestWeight 1) k (lowHeightRoots γ₀ c Kset) x‖ ^ 2 *
      (1 + |x.re|) ^ (3 + E) ≤ clusterTailConstant H |γ₀| N₀ n := by
  have hH0 : 0 ≤ H := by linarith
  have hKr : ∀ r ∈ pairRoots (Kset.toList.map fun ρ => gammaOf ρ - γ₀),
      ‖x - r‖ ≤ (H + 1) * (1 + |x.re|) := by
    intro r hr
    obtain ⟨s, hs, hrs⟩ := mem_pairRoots.mp hr
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hρZ, hρH⟩ := hK ρ (Finset.mem_toList.mp hρ)
    have hst := Z.strip ρ hρZ
    have hre : |(gammaOf ρ - γ₀).re| ≤ H := by
      rw [Complex.sub_re, WeilEF.gammaOf_re, Complex.ofReal_re]; exact hρH
    have him : |(gammaOf ρ - γ₀).im| ≤ 1 / 2 := by
      rw [Complex.sub_im, WeilEF.gammaOf_im, Complex.ofReal_im, sub_zero, abs_le]
      constructor <;> linarith [hst.1, hst.2]
    rcases hrs with rfl | rfl
    · exact norm_sub_root_le hx hre him hH0 le_rfl
    · exact norm_sub_root_le hx (by rw [Complex.conj_re]; exact hre)
        (by rw [Complex.conj_im, abs_neg]; exact him) hH0 le_rfl
  have hpre : |(⟨-γ₀, 1 / 2⟩ : ℂ).re| ≤ |γ₀| := by simp
  have hpim : |(⟨-γ₀, 1 / 2⟩ : ℂ).im| ≤ 1 / 2 := by norm_num [abs_of_pos]
  have hp := norm_sub_root_le (H := |γ₀|) hx hpre hpim (abs_nonneg _) le_rfl
  have hp' := norm_sub_root_le (H := |γ₀|) (r := conj (⟨-γ₀, 1 / 2⟩ : ℂ)) hx
    (by rw [Complex.conj_re]; exact hpre) (by rw [Complex.conj_im, abs_neg]; exact hpim)
    (abs_nonneg _) le_rfl
  have hcabs : |c| ≤ H := (abs_le.mpr hcδ).trans (by linarith)
  have hcre : |((c : ℂ)).re| ≤ H := by simpa using hcabs
  have hcim : |((c : ℂ)).im| ≤ 1 / 2 := by simp
  have hc := norm_sub_root_le hx hcre hcim hH0 le_rfl
  have hc' : ‖x - conj (c : ℂ)‖ ≤ (H + 1) * (1 + |x.re|) := by rw [Complex.conj_ofReal]; exact hc
  exact norm_sq_lowHeightProfile_tail_split hH0 (abs_nonneg γ₀) hx hKr hp hp' hc hc' hk
    (by rw [List.length_map, Finset.length_toList]; exact hKn) hE


/-! ### Re-centred selection -/

/-- `ε₀/(2(4λ)^{⌊log₂ n⌋+1})`, the killing distance produced by the halving selection, with
`ε₀ = lowHeightEps0 δ N₀` and `λ = lowHeightScale n`. -/
def clusterKillScale (δ : ℝ) (N₀ n : ℕ) : ℝ :=
  lowHeightEps0 δ N₀ / (2 * (4 * lowHeightScale n) ^ (Nat.log 2 n + 1))

/-- The floor for the deep-zero value of the cluster-robust profile. -/
def clusterFloor (δ : ℝ) (N₀ n : ℕ) : ℝ :=
  unitWeightFloor ^ (2 * N₀) * clusterKillScale δ N₀ n ^ (4 * n) * (δ / 2) ^ 4

theorem lowHeightEps0_pos {δ : ℝ} (hδ : 0 < δ) (N₀ : ℕ) : 0 < lowHeightEps0 δ N₀ := by
  unfold lowHeightEps0; have := lt_min hδ one_pos; positivity

theorem lowHeightEps0_le {δ : ℝ} (hδ : 0 < δ) (N₀ : ℕ) :
    lowHeightEps0 δ N₀ ≤ δ / 300 ∧ lowHeightEps0 δ N₀ ≤ 1 / 300 := by
  unfold lowHeightEps0
  have hden : (300 : ℝ) ≤ 100 * (3 * N₀ + 3) := by nlinarith [Nat.cast_nonneg (α := ℝ) N₀]
  have h1 := min_le_left δ 1
  have h2 := min_le_right δ 1
  have hm0 : 0 ≤ min δ 1 := le_min hδ.le zero_le_one
  constructor
  · calc min δ 1 / (100 * (3 * N₀ + 3)) ≤ δ / (100 * (3 * N₀ + 3)) := by gcongr
      _ ≤ δ / 300 := div_le_div_of_nonneg_left hδ.le (by norm_num) hden
  · calc min δ 1 / (100 * (3 * N₀ + 3)) ≤ 1 / (100 * (3 * N₀ + 3)) := by gcongr
      _ ≤ 1 / 300 := div_le_div_of_nonneg_left zero_le_one (by norm_num) hden

theorem lowHeightEps0_half_le {δ δ₁ : ℝ} (hδ₁ : δ / 2 ≤ δ₁) (N₀ : ℕ) :
    lowHeightEps0 δ N₀ / 2 ≤ lowHeightEps0 δ₁ N₀ := by
  unfold lowHeightEps0
  have hm : min δ 1 / 2 ≤ min δ₁ 1 := by
    rw [le_min_iff]
    constructor
    · linarith [min_le_left δ 1]
    · linarith [min_le_right δ 1]
  have hden : 0 < 100 * (3 * (N₀ : ℝ) + 3) := by positivity
  rw [div_div, mul_comm (100 * (3 * (N₀ : ℝ) + 3)), ← div_div]
  gcongr

theorem clusterKillScale_pos {δ : ℝ} (hδ : 0 < δ) (N₀ n : ℕ) : 0 < clusterKillScale δ N₀ n := by
  unfold clusterKillScale lowHeightScale
  have := lowHeightEps0_pos hδ N₀
  positivity

/-- **Re-centred selection.**  Around a zero `ρ₀ = ½ + δ + iγ₀`, with at most `n` zeros in the
window `|γ - γ₀| ≤ H + 1`, the halving selection finds a zero `ρ₁ = ½ + δ₁ + iγ₁` with
`δ₁ ≥ δ/2` and `|γ₁ - γ₀| ≤ ε₀`, a cluster radius `ε` and a killing distance `η = λε` bounded
below by `clusterKillScale δ N₀ n`, such that every zero of the window `|γ - γ₁| ≤ H` is either
within `ε` of `±iδ₁` (in coordinates centred at `γ₁`) or at distance `≥ η` from both. -/
theorem cluster_selection (Z : ZeroConfig) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ)
    (hre : ρ₀.re = 1 / 2 + δ) {H : ℝ} (hH : 0 ≤ H) {N₀ n : ℕ}
    (hn : (Z.finite_window (ρ₀.im - (H + 1)) (ρ₀.im + (H + 1))).toFinset.card ≤ n) :
    ∃ ρ₁ ∈ Z.carrier, ∃ δ₁ : ℝ, ρ₁.re = 1 / 2 + δ₁ ∧ δ / 2 ≤ δ₁ ∧
      |ρ₁.im - ρ₀.im| ≤ lowHeightEps0 δ N₀ ∧
      ∃ Kset ⊆ (Z.finite_window (ρ₁.im - H) (ρ₁.im + H)).toFinset, Kset.card ≤ n ∧
        ∃ ε η : ℝ, 0 < ε ∧ ε ≤ lowHeightEps0 δ₁ N₀ ∧ η ≤ 1 ∧ clusterKillScale δ N₀ n ≤ η ∧
          ε / η = 1 / lowHeightScale n ∧
          (∀ ρ ∈ (Z.finite_window (ρ₁.im - H) (ρ₁.im + H)).toFinset, ρ ∉ Kset →
            ‖(gammaOf ρ - ρ₁.im) - -(I * δ₁)‖ < ε ∨ ‖(gammaOf ρ - ρ₁.im) - I * δ₁‖ < ε) ∧
          (∀ ρ ∈ Kset,
            η ≤ ‖(gammaOf ρ - ρ₁.im) - -(I * δ₁)‖ ∧ η ≤ ‖(gammaOf ρ - ρ₁.im) - I * δ₁‖) := by
  classical
  set γ₀ := ρ₀.im with hγ₀
  set W₁ := (Z.finite_window (γ₀ - (H + 1)) (γ₀ + (H + 1))).toFinset with hW₁def
  have hW₁ : ∀ ρ, ρ ∈ W₁ ↔ ρ ∈ Z.carrier ∧ γ₀ - (H + 1) < ρ.im ∧ ρ.im ≤ γ₀ + (H + 1) := by
    intro ρ; rw [hW₁def, Set.Finite.mem_toFinset]; rfl
  set xf : ℂ → ℂ := fun ρ => gammaOf ρ - γ₀ with hxf
  set P := W₁.image xf with hP
  have hPcard : P.card ≤ n := Finset.card_image_le.trans hn
  set s := lowHeightEps0 δ N₀ with hs
  have hs0 : 0 < s := lowHeightEps0_pos hδ N₀
  obtain ⟨hsδ, hs1⟩ := lowHeightEps0_le hδ N₀
  set lam := lowHeightScale n with hlamdef
  have hlam : 1 ≤ lam := by
    rw [hlamdef]; unfold lowHeightScale; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  set kk := Nat.log 2 n + 1 with hkk
  have hx₀ : xf ρ₀ = -(I * δ) := (gammaOf_sub_of_re_im (γ₀ := γ₀) rfl hre).1
  have hx₀P : -(I * (δ : ℂ)) ∈ P := by
    rw [← hx₀]
    exact Finset.mem_image_of_mem xf ((hW₁ ρ₀).mpr ⟨hρ₀, by linarith, by linarith⟩)
  have hcardk : (P.filter fun q => ‖q - -(I * (δ : ℂ))‖ < s).card ≤ 2 ^ kk :=
    (Finset.card_filter_le _ _).trans (hPcard.trans (Nat.lt_pow_succ_log_self one_lt_two n).le)
  obtain ⟨c, hcP, t, ht1, ht2, ht3, ht4⟩ :=
    exists_empty_annulus_center P hlam kk (-(I * δ)) s hx₀P hs0 hcardk
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  obtain ⟨ρ₁, hρ₁W, hρ₁c⟩ := Finset.mem_image.mp hcP
  have hρ₁Z := ((hW₁ ρ₁).mp hρ₁W).1
  set δ₁ := ρ₁.re - 1 / 2 with hδ₁def
  have hcre : c.re = ρ₁.im - γ₀ := by rw [← hρ₁c]; simp [hxf, WeilEF.gammaOf_re]
  have hcim : c.im = -δ₁ := by rw [← hρ₁c]; simp [hxf, WeilEF.gammaOf_im, hδ₁def]
  have hcnear : ‖c - -(I * (δ : ℂ))‖ < s := by linarith
  have hre_near : |ρ₁.im - γ₀| < s := by
    have := Complex.abs_re_le_norm (c - -(I * (δ : ℂ)))
    rw [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, hcre] at this
    simp only [zero_mul, mul_zero, sub_zero, neg_zero] at this
    linarith
  have him_near : |δ - δ₁| < s := by
    have := Complex.abs_im_le_norm (c - -(I * (δ : ℂ)))
    rw [Complex.sub_im, Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, hcim] at this
    simp only [zero_mul, one_mul, zero_add] at this
    rw [abs_sub_comm]
    have e : -δ₁ - -δ = δ - δ₁ := by ring
    rw [e] at this
    rw [abs_sub_comm]; linarith
  have hδ₁ : δ / 2 ≤ δ₁ := by
    have := (abs_lt.mp him_near).2
    linarith
  -- the new window
  set W := (Z.finite_window (ρ₁.im - H) (ρ₁.im + H)).toFinset with hWdef
  have hW : ∀ ρ, ρ ∈ W ↔ ρ ∈ Z.carrier ∧ ρ₁.im - H < ρ.im ∧ ρ.im ≤ ρ₁.im + H := by
    intro ρ; rw [hWdef, Set.Finite.mem_toFinset]; rfl
  have hWW₁ : W ⊆ W₁ := by
    intro ρ hρ
    obtain ⟨hρZ, h1, h2⟩ := (hW ρ).mp hρ
    have := abs_lt.mp hre_near
    exact (hW₁ ρ).mpr ⟨hρZ, by linarith, by linarith⟩
  have hrefl : ∀ ρ ∈ W₁, reflect ρ ∈ W₁ := by
    intro ρ hρ
    obtain ⟨hρZ, h1, h2⟩ := (hW₁ ρ).mp hρ
    exact (hW₁ _).mpr ⟨Z.reflect_mem ρ hρZ, by rw [Tail.reflect_im]; exact h1,
      by rw [Tail.reflect_im]; exact h2⟩
  -- coordinates centred at `γ₁`
  have hid1 : ∀ ρ : ℂ, (gammaOf ρ - ρ₁.im) - -(I * δ₁) = xf ρ - c := by
    intro ρ
    apply Complex.ext
    · simp [hxf, hcre]
    · simp [hxf, hcim]
  have hid2 : ∀ ρ : ℂ, ‖(gammaOf ρ - ρ₁.im) - I * δ₁‖ = ‖xf (reflect ρ) - c‖ := by
    intro ρ
    have : (gammaOf ρ - ρ₁.im) - I * δ₁ = conj (xf (reflect ρ) - c) := by
      rw [hxf]
      simp only [Tail.gammaOf_reflect, map_sub, Complex.conj_conj, Complex.conj_ofReal]
      apply Complex.ext
      · simp [hcre]
      · simp [hcim]
    rw [this, Complex.norm_conj]
  set ε := t / (2 * lam) with hεdef
  set η := t / 2 with hηdef
  set Kset := W.filter (fun ρ => η ≤ ‖(gammaOf ρ - ρ₁.im) - -(I * δ₁)‖ ∧
    η ≤ ‖(gammaOf ρ - ρ₁.im) - I * δ₁‖) with hKdef
  have hlam0 : 0 < lam := by linarith
  refine ⟨ρ₁, hρ₁Z, δ₁, by rw [hδ₁def]; ring, hδ₁, hre_near.le, Kset, Finset.filter_subset _ _,
    ((Finset.card_filter_le _ _).trans (Finset.card_le_card hWW₁)).trans hn, ε, η,
    by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : ε ≤ s / 2 := by
      rw [hεdef, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    exact h1.trans (lowHeightEps0_half_le hδ₁ N₀)
  · rw [hηdef]; linarith
  · unfold clusterKillScale
    rw [← hs, ← hlamdef, ← hkk, hηdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    have h := ht1
    rw [div_le_iff₀ (by positivity)] at h
    nlinarith
  · rw [hεdef, hηdef]; field_simp
  · intro ρ hρ hK
    have hnot : ¬ (η ≤ ‖(gammaOf ρ - ρ₁.im) - -(I * δ₁)‖ ∧
        η ≤ ‖(gammaOf ρ - ρ₁.im) - I * δ₁‖) := fun h => hK (Finset.mem_filter.mpr ⟨hρ, h⟩)
    rw [not_and_or, not_le, not_le] at hnot
    rcases hnot with h | h
    · left
      rw [hid1] at h ⊢
      exact ht4 _ (Finset.mem_image_of_mem xf (hWW₁ hρ)) h
    · right
      rw [hid2] at h ⊢
      exact ht4 _ (Finset.mem_image_of_mem xf (hrefl _ (hWW₁ hρ))) h
  · intro ρ hρ
    exact (Finset.mem_filter.mp hρ).2


/-! ### The cluster-robust theorem -/

/-- **Cluster-robust Weil criterion.**  Let `Z` be a zero configuration with local count
`N(t, t+1] ≤ A₀ log(|t| + 3)` and `ρ₀ = ½ + δ + iγ₀` a zero with `δ > 0`, `|γ₀| ≥ 2`.  If the
window `|γ - γ₀| ≤ H + 1` contains at most `n` distinct zeros, `2n + 7 ≤ N₀ ≤ a`, and
`clusterTailConstant H (|γ₀| + 1) N₀ n · 24A₀ log(|γ₀| + 4) <
  (79/50)(1 + H)^{4N₀ - 4n - 11} · clusterFloor δ N₀ n`,
then the level-`a` Hodge index fails.

Unlike `exists_hodge_violation_low_height`, the centre of the test is not `ρ₀` but a zero `ρ₁`
near it chosen by halving (`cluster_selection`): the killing distance is then
`ε₀/(2(4λ)^{⌊log₂ n⌋+1})` instead of `ε₀/λ^n`, and the polar root enters the tail with the
power `4` instead of `4n + 8`. -/
theorem exists_hodge_violation_cluster_robust (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    (hγ : 2 ≤ |ρ₀.im|) {H a : ℝ} (hH : 1 ≤ H) {N₀ n : ℕ} (hN₀a : (N₀ : ℝ) ≤ a)
    (hn : (Z.finite_window (ρ₀.im - (H + 1)) (ρ₀.im + (H + 1))).toFinset.card ≤ n)
    (hNn : 2 * n + 7 ≤ N₀)
    (hbig : clusterTailConstant H (|ρ₀.im| + 1) N₀ n * (24 * A₀ * Real.log (|ρ₀.im| + 4)) <
      79 / 50 * (1 + H) ^ (4 * N₀ - 4 * n - 11) * clusterFloor δ N₀ n) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
      paperFT f (-(I / 2)) = 0 ∧ (Z.W f f).re < 0 := by
  classical
  obtain ⟨ρ₁, hρ₁, δ₁, hre₁, hδ₁, hγ₁, Kset, hKW, hKn, ε, η, hε0, hεε, hη1, hηlow, hεη, hclu,
    hkil⟩ := cluster_selection (N₀ := N₀) Z hρ₀ hδ hre (by linarith) hn
  have hst := Z.strip ρ₁ hρ₁
  have hδ₁0 : 0 < δ₁ := by linarith
  have hδ₁2 : δ₁ ≤ 1 / 2 := by linarith [hst.2]
  obtain ⟨hsδ, hs1⟩ := lowHeightEps0_le hδ N₀
  have hγ₁' : 1 ≤ |ρ₁.im| := by
    have := abs_sub_abs_le_abs_sub ρ₀.im ρ₁.im
    rw [abs_sub_comm] at hγ₁
    linarith
  have hγ₁'' : |ρ₁.im| ≤ |ρ₀.im| + 1 := by
    have := abs_sub_abs_le_abs_sub ρ₁.im ρ₀.im
    linarith
  have hη0 : 0 < η := lt_of_lt_of_le (clusterKillScale_pos hδ N₀ n) hηlow
  have hε1 : ε ≤ 1 := by
    obtain ⟨-, h⟩ := lowHeightEps0_le hδ₁0 N₀
    linarith
  have hWn : ∀ ρ, ρ ∈ (Z.finite_window (ρ₁.im - H) (ρ₁.im + H)).toFinset ↔
      ρ ∈ Z.carrier ∧ ρ₁.im - H < ρ.im ∧ ρ.im ≤ ρ₁.im + H := by
    intro ρ; rw [Set.Finite.mem_toFinset]; rfl
  have hS : (N₀ : ℝ) * (4 * ε) + (2 * (n : ℝ)) * (ε / η) + 2 * ε + 2 * ε / δ₁ ≤ 1 / 20 := by
    rw [hεη]; exact lowHeight_scale_bound hδ₁0 hε0.le hεε
  -- the phase
  obtain ⟨c, hc, hcre⟩ := exists_phase_rotation hδ₁0
    (paperFT (fun u => (sinhTestWeight 1 u : ℂ)) (-(I * δ₁)) ^
        (N₀ - (2 * (Kset.card + 2) + 1) + 2 * (Kset.card + 2) + 1) *
      ((Kset.toList.map (fun ρ => gammaOf ρ - ρ₁.im) ++ [(⟨-ρ₁.im, 1 / 2⟩ : ℂ)]).map
        (fun r => (-(I * δ₁) - r) * (-(I * δ₁) - conj r))).prod)
  have hLlen := lowHeightRoots_length ρ₁.im c Kset
  have hk : N₀ - (2 * (Kset.card + 2) + 1) + 2 * (lowHeightRoots ρ₁.im c Kset).length + 1 =
      N₀ := by
    rw [hLlen]; omega
  have hF0re : (lowHeightProfile (sinhTestWeight 1) (N₀ - (2 * (Kset.card + 2) + 1))
      (lowHeightRoots ρ₁.im c Kset) (-(I * δ₁))).re = 0 := by
    rw [lowHeightProfile_x₀_eq, hLlen, mul_comm]
    exact hcre
  -- the test
  obtain ⟨hfc, hfs, hff⟩ := lowHeightTest_props (sinhTestWeight_contDiff 1)
    (sinhTestWeight_even 1) (sinhTestWeight_supp zero_le_one) ρ₁.im
    (N₀ - (2 * (Kset.card + 2) + 1)) (lowHeightRoots ρ₁.im c Kset)
  refine ⟨lowHeightTest ρ₁.im (sinhTestWeight 1) (N₀ - (2 * (Kset.card + 2) + 1))
    (lowHeightRoots ρ₁.im c Kset), hfc, ?_, ?_, ?_, ?_⟩
  · refine tsupport_subset_of_support_subset_abs fun u hu => ?_
    have h := hfs u hu
    have e : (((N₀ - (2 * (Kset.card + 2) + 1) : ℕ) : ℝ) +
        2 * ((lowHeightRoots ρ₁.im c Kset).length : ℝ) + 1) * 1 = (N₀ : ℝ) := by
      rw [mul_one]; exact_mod_cast hk
    rw [e] at h
    linarith
  · rw [hff]
    have : I / 2 - (ρ₁.im : ℂ) = (⟨-ρ₁.im, 1 / 2⟩ : ℂ) := by apply Complex.ext <;> simp
    rw [this]
    exact lowHeightProfile_eq_zero_of_mem (by unfold lowHeightRoots; simp)
  · rw [hff]
    have : -(I / 2) - (ρ₁.im : ℂ) = conj (⟨-ρ₁.im, 1 / 2⟩ : ℂ) := by apply Complex.ext <;> simp
    rw [this]
    exact lowHeightProfile_eq_zero_of_conj_mem (by unfold lowHeightRoots; simp)
  · have hKH : ∀ σ ∈ Kset, σ ∈ Z.carrier ∧ |σ.im - ρ₁.im| ≤ H := by
      intro σ hσ
      obtain ⟨hσZ, h1, h2⟩ := (hWn σ).mp (hKW hσ)
      exact ⟨hσZ, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    have hW := re_W_lowHeightTest_le Z hA₀ hloc hρ₁ hδ₁0 hδ₁2 hre₁ hγ₁' hH hWn hKn hε0 hε1 hη0
      hclu hkil hS hk hF0re (E := 4 * N₀ - 4 * n - 11)
      (lowHeight_tail_bound_split Z (by linarith) hc hδ₁2 hKH hk hKn (by omega))
    have hfloor := norm_sq_lowHeightProfile_x₀_ge hδ₁0 hγ₁' hη0 hη1 hKn hkil hk
    set F2 := ‖lowHeightProfile (sinhTestWeight 1) (N₀ - (2 * (Kset.card + 2) + 1))
      (lowHeightRoots ρ₁.im c Kset) (-(I * δ₁))‖ ^ 2 with hF2
    have hcf : clusterFloor δ N₀ n ≤ F2 := by
      refine le_trans ?_ hfloor
      unfold clusterFloor
      have := unitWeightFloor_pos
      have := (clusterKillScale_pos hδ N₀ n).le
      gcongr
    have hHE : 0 < (1 + H) ^ (4 * N₀ - 4 * n - 11) := by positivity
    have hA0 : 0 < A₀ := by linarith
    have hlog : Real.log (|ρ₁.im| + 3) ≤ Real.log (|ρ₀.im| + 4) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog0 : 0 ≤ Real.log (|ρ₁.im| + 3) :=
      Real.log_nonneg (by linarith [abs_nonneg ρ₁.im])
    have hT : clusterTailConstant H |ρ₁.im| N₀ n ≤ clusterTailConstant H (|ρ₀.im| + 1) N₀ n := by
      unfold clusterTailConstant
      gcongr
    have hT0 : 0 ≤ clusterTailConstant H |ρ₁.im| N₀ n := by
      unfold clusterTailConstant; positivity
    have hprod : clusterTailConstant H |ρ₁.im| N₀ n * (24 * A₀ * Real.log (|ρ₁.im| + 3)) ≤
        clusterTailConstant H (|ρ₀.im| + 1) N₀ n * (24 * A₀ * Real.log (|ρ₀.im| + 4)) := by
      have : 0 ≤ clusterTailConstant H (|ρ₀.im| + 1) N₀ n := hT0.trans hT
      gcongr
    have hkey : clusterTailConstant H |ρ₁.im| N₀ n / (1 + H) ^ (4 * N₀ - 4 * n - 11) *
        (24 * A₀ * Real.log (|ρ₁.im| + 3)) < 79 / 50 * F2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hHE]
      nlinarith
    linarith

/-! ### The horizon -/

theorem exp_numeric_bounds : (101 : ℝ) ≤ Real.exp 5 ∧ (24 : ℝ) ≤ Real.exp 4 ∧
    (400 : ℝ) ≤ Real.exp 6 ∧ (800 : ℝ) ≤ Real.exp 7 ∧ Real.exp 2 ≤ 15 / 2 ∧
    (2 : ℝ) ≤ Real.exp 1 := by
  have he := Real.exp_one_gt_d9
  have he' := Real.exp_one_lt_d9
  have e : ∀ k : ℕ, Real.exp k = Real.exp 1 ^ k := fun k => by rw [← Real.exp_nat_mul, mul_one]
  have lo : ∀ k : ℕ, (2.7182818283 : ℝ) ^ k ≤ Real.exp k := fun k => by
    rw [e k]; exact pow_le_pow_left₀ (by norm_num) he.le k
  refine ⟨?_, ?_, ?_, ?_, ?_, by linarith⟩
  · have := lo 5; norm_num at this ⊢; linarith
  · have := lo 4; norm_num at this ⊢; linarith
  · have := lo 6; norm_num at this ⊢; linarith
  · have := lo 7; norm_num at this ⊢; linarith
  · have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by exact_mod_cast e 2
    rw [h2]
    have : Real.exp 1 ^ 2 ≤ (2.7182818286 : ℝ) ^ 2 := pow_le_pow_left₀ (Real.exp_pos 1).le he'.le 2
    norm_num at this ⊢; linarith

/-- `⌊log₂ n⌋ ≤ 2 log a` when `n ≤ a` and `1 ≤ a`. -/
theorem natLog_two_le_two_log {n : ℕ} {a : ℝ} (ha : 1 ≤ a) (hn : (n : ℝ) ≤ a) :
    (Nat.log 2 n : ℝ) ≤ 2 * Real.log a := by
  have hl : 0 ≤ Real.log a := Real.log_nonneg ha
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp only [Nat.log_zero_right, Nat.cast_zero]; linarith
  set m := Nat.log 2 n
  have h2m : ((2 : ℕ) ^ m : ℕ) ≤ n := Nat.pow_log_le_self 2 hpos.ne'
  have h2m' : (2 : ℝ) ^ m ≤ a := by
    have : ((2 ^ m : ℕ) : ℝ) ≤ n := by exact_mod_cast h2m
    push_cast at this; linarith
  have hexp : Real.exp ((m : ℝ) * (1 / 2)) ≤ a := by
    rw [Real.exp_nat_mul]
    exact (pow_le_pow_left₀ (Real.exp_pos _).le exp_one_half_lt_two.le m).trans h2m'
  have := Real.log_le_log (Real.exp_pos _) hexp
  rw [Real.log_exp] at this
  linarith


/-- For `a ≥ e⁶`, `a ≥ 1/δ`, `N₀ ≤ a` and `n + 1 ≤ a`, the killing distance of the halving
selection is at least `exp(-5 log² a)`. -/
theorem clusterKillScale_ge {δ a : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (ha6 : Real.exp 6 ≤ a)
    (haδ : 1 / δ ≤ a) {N₀ n : ℕ} (hN₀ : (N₀ : ℝ) ≤ a) (hn : (n : ℝ) + 1 ≤ a) :
    Real.exp (-(5 * Real.log a ^ 2)) ≤ clusterKillScale δ N₀ n := by
  obtain ⟨-, -, e6, e7, -, -⟩ := exp_numeric_bounds
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 6) ha6
  set ℓ := Real.log a with hℓ
  have hℓ6 : 6 ≤ ℓ := by
    have := Real.log_le_log (Real.exp_pos 6) ha6; rwa [Real.log_exp] at this
  have hae : Real.exp ℓ = a := Real.exp_log ha0
  have ha1 : 1 ≤ a := by linarith
  set m := Nat.log 2 n with hm
  have hm2 : (m : ℝ) ≤ 2 * ℓ := natLog_two_le_two_log ha1 (by linarith)
  unfold clusterKillScale lowHeightEps0 lowHeightScale
  rw [min_eq_left (by linarith), ← hm]
  -- the three factors
  have hD1 : 2 * (100 * (3 * (N₀ : ℝ) + 3)) ≤ Real.exp (7 + ℓ) := by
    rw [Real.exp_add, hae]; nlinarith
  have hbase : 4 * (100 * ((n : ℝ) + 1)) ≤ Real.exp (6 + ℓ) := by
    rw [Real.exp_add, hae]; nlinarith
  have hD2 : (4 * (100 * ((n : ℝ) + 1))) ^ (m + 1) ≤ Real.exp (((m + 1 : ℕ) : ℝ) * (6 + ℓ)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hδe : Real.exp (-ℓ) ≤ δ := by
    rw [Real.exp_neg, hae]
    rw [div_le_iff₀ hδ] at haδ
    rw [inv_le_iff_one_le_mul₀ ha0]; linarith
  have hexp : -(5 * ℓ ^ 2) + (((m + 1 : ℕ) : ℝ) * (6 + ℓ)) + (7 + ℓ) ≤ -ℓ := by
    push_cast
    nlinarith
  have hD1p : 0 < 2 * (100 * (3 * (N₀ : ℝ) + 3)) := by positivity
  have hD2p : 0 < (4 * (100 * ((n : ℝ) + 1))) ^ (m + 1) := by positivity
  have e : δ / (100 * (3 * (N₀ : ℝ) + 3)) / (2 * (4 * (100 * ((n : ℝ) + 1))) ^ (m + 1)) =
      δ / (2 * (100 * (3 * (N₀ : ℝ) + 3)) * (4 * (100 * ((n : ℝ) + 1))) ^ (m + 1)) := by
    rw [div_div]; ring_nf
  rw [e, le_div_iff₀ (by positivity)]
  calc Real.exp (-(5 * ℓ ^ 2)) * (2 * (100 * (3 * (N₀ : ℝ) + 3)) *
        (4 * (100 * ((n : ℝ) + 1))) ^ (m + 1))
      ≤ Real.exp (-(5 * ℓ ^ 2)) * (Real.exp (7 + ℓ) *
          Real.exp (((m + 1 : ℕ) : ℝ) * (6 + ℓ))) := by gcongr
    _ = Real.exp (-(5 * ℓ ^ 2) + (((m + 1 : ℕ) : ℝ) * (6 + ℓ)) + (7 + ℓ)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-ℓ) := Real.exp_le_exp.mpr hexp
    _ ≤ δ := hδe


/-- `(G + 2)⁴ · 24A₀ log(G + 4) ≤ exp(4 + 5 log(A₀(G + 4)))`. -/
theorem tail_prefactor_le_exp {A₀ G : ℝ} (hA₀ : 1 ≤ A₀) (hG : 0 ≤ G) :
    (G + 1 + 1) ^ 4 * (24 * A₀ * Real.log (G + 4)) ≤
      Real.exp (4 + 5 * Real.log (A₀ * (G + 4))) := by
  obtain ⟨-, e4, -, -, -, -⟩ := exp_numeric_bounds
  have hG4 : 0 < G + 4 := by linarith
  have hA0 : 0 < A₀ := by linarith
  have hlA : 0 ≤ Real.log A₀ := Real.log_nonneg hA₀
  have hl4 : 0 ≤ Real.log (G + 4) := Real.log_nonneg (by linarith)
  have hsplit : Real.log (A₀ * (G + 4)) = Real.log A₀ + Real.log (G + 4) :=
    Real.log_mul hA0.ne' hG4.ne'
  have h1 : (G + 1 + 1) ^ 4 ≤ Real.exp (4 * Real.log (G + 4)) := by
    rw [show (4 : ℝ) * Real.log (G + 4) = ((4 : ℕ) : ℝ) * Real.log (G + 4) by norm_num,
      Real.exp_nat_mul, Real.exp_log hG4]
    exact pow_le_pow_left₀ (by linarith) (by linarith) 4
  have h2 : Real.log (G + 4) ≤ Real.exp (Real.log (G + 4)) := by
    rw [Real.exp_log hG4]; exact Real.log_le_self hG4.le
  have h3 : A₀ = Real.exp (Real.log A₀) := (Real.exp_log hA0).symm
  calc (G + 1 + 1) ^ 4 * (24 * A₀ * Real.log (G + 4))
      ≤ Real.exp (4 * Real.log (G + 4)) *
          (Real.exp 4 * Real.exp (Real.log A₀) * Real.exp (Real.log (G + 4))) := by
        rw [← h3]
        gcongr
    _ = Real.exp (4 + (5 * Real.log (G + 4) + Real.log A₀)) := by
        simp only [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (4 + 5 * Real.log (A₀ * (G + 4))) := by
        apply Real.exp_le_exp.mpr
        rw [hsplit]; nlinarith

/-- The linear bookkeeping of the horizon condition. -/
theorem cluster_horizon_linear {a ℓ Λ : ℝ} {n N₀ : ℕ} (hℓ6 : 6 ≤ ℓ) (hΛ0 : 0 ≤ Λ)
    (hsize : 100 * (((n : ℝ) + 1) * ℓ ^ 2 + Λ) ≤ a) (hN : a - 1 < N₀) :
    (n : ℝ) + 1 ≤ a ∧ 2 * n + 7 ≤ N₀ ∧
      ((8 * n + 15 : ℕ) : ℝ) * 5 + (4 + 5 * Λ) <
        ((2 * N₀ : ℕ) : ℝ) * 2 + ((4 * n : ℕ) : ℝ) * (-(5 * ℓ ^ 2)) + ((4 : ℕ) : ℝ) * (-ℓ - 1) := by
  have hℓ2 : 36 ≤ ℓ ^ 2 := by nlinarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnl : 36 * ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) * ℓ ^ 2 := by nlinarith
  have hnl' : 36 * (n : ℝ) ≤ (n : ℝ) * ℓ ^ 2 := by nlinarith
  refine ⟨by nlinarith, ?_, ?_⟩
  · have : ((2 * n + 7 : ℕ) : ℝ) < N₀ := by push_cast; nlinarith
    exact_mod_cast this.le
  · push_cast
    have hℓl : ℓ ≤ ℓ ^ 2 := by nlinarith
    nlinarith

/-- The lower side of the horizon condition, after multiplication by `101^{4n+11}`. -/
theorem cluster_horizon_lower {B U κ δ ℓ : ℝ} {n N₀ : ℕ} (hB0 : 0 < B) (hκ0 : 0 ≤ κ)
    (hBQ : B ^ (2 * N₀) * Real.exp (((2 * N₀ : ℕ) : ℝ) * 2) ≤ (101 : ℝ) ^ (4 * N₀) * U ^ (2 * N₀))
    (hκ4 : Real.exp (((4 * n : ℕ) : ℝ) * (-(5 * ℓ ^ 2))) ≤ κ ^ (4 * n))
    (hδ4 : Real.exp (((4 : ℕ) : ℝ) * (-ℓ - 1)) ≤ (δ / 2) ^ 4) (hU : 0 ≤ U) :
    B ^ (2 * N₀) * Real.exp (((2 * N₀ : ℕ) : ℝ) * 2 + ((4 * n : ℕ) : ℝ) * (-(5 * ℓ ^ 2)) +
        ((4 : ℕ) : ℝ) * (-ℓ - 1)) ≤
      (101 : ℝ) ^ (4 * N₀) * U ^ (2 * N₀) * κ ^ (4 * n) * (δ / 2) ^ 4 := by
  rw [Real.exp_add, Real.exp_add, ← mul_assoc, ← mul_assoc]
  have h1 : 0 ≤ B ^ (2 * N₀) * Real.exp (((2 * N₀ : ℕ) : ℝ) * 2) := by positivity
  have h2 : 0 ≤ Real.exp (((4 * n : ℕ) : ℝ) * (-(5 * ℓ ^ 2))) := (Real.exp_pos _).le
  have h3 : 0 ≤ Real.exp (((4 : ℕ) : ℝ) * (-ℓ - 1)) := (Real.exp_pos _).le
  have h4 : 0 ≤ (101 : ℝ) ^ (4 * N₀) * U ^ (2 * N₀) := by positivity
  have h5 : 0 ≤ κ ^ (4 * n) := pow_nonneg hκ0 _
  exact mul_le_mul (mul_le_mul hBQ hκ4 h2 h4) hδ4 h3 (mul_nonneg h4 h5)

/-- **The horizon condition.**  If `a ≥ e⁶`, `a ≥ 1/δ` and
`100((n + 1) log² a + log(A₀(G + 4))) ≤ a`, then `N₀ = ⌊a⌋₊` satisfies `2n + 7 ≤ N₀` and the size
condition of `exists_hodge_violation_cluster_robust` with `H = 100` holds. -/
theorem cluster_horizon_condition {A₀ G δ a : ℝ} (hA₀ : 1 ≤ A₀) (hG : 0 ≤ G) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) (ha6 : Real.exp 6 ≤ a) (haδ : 1 / δ ≤ a) {n : ℕ}
    (hsize : 100 * (((n : ℝ) + 1) * Real.log a ^ 2 + Real.log (A₀ * (G + 4))) ≤ a) :
    2 * n + 7 ≤ ⌊a⌋₊ ∧
      clusterTailConstant 100 (G + 1) ⌊a⌋₊ n * (24 * A₀ * Real.log (G + 4)) <
        79 / 50 * (1 + 100) ^ (4 * ⌊a⌋₊ - 4 * n - 11) * clusterFloor δ ⌊a⌋₊ n := by
  obtain ⟨e5, -, e6, -, e2, e1⟩ := exp_numeric_bounds
  set N₀ := ⌊a⌋₊ with hN₀def
  set ℓ := Real.log a with hℓ
  set Λ := Real.log (A₀ * (G + 4)) with hΛ
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 6) ha6
  have hℓ6 : 6 ≤ ℓ := by
    have := Real.log_le_log (Real.exp_pos 6) ha6; rwa [Real.log_exp] at this
  have hΛ0 : 0 ≤ Λ := Real.log_nonneg (by nlinarith)
  have hN₀a : (N₀ : ℝ) ≤ a := Nat.floor_le ha0.le
  have hN₀a' : a - 1 < N₀ := Nat.sub_one_lt_floor a
  obtain ⟨hn1, h2n7, hlin⟩ := cluster_horizon_linear (N₀ := N₀) hℓ6 hΛ0 hsize hN₀a'
  refine ⟨h2n7, ?_⟩
  have hκ := clusterKillScale_ge hδ hδ2 ha6 haδ hN₀a hn1
  set κ := clusterKillScale δ N₀ n with hκdef
  have hκ0 : 0 ≤ κ := (Real.exp_pos _).le.trans hκ
  set U := unitWeightFloor with hUdef
  have hU := unitWeightFloor_ge
  set B := Real.exp (1 / 2) * 168 with hBdef
  have hB0 : 0 < B := by positivity
  have hB : B ≤ 336 := by rw [hBdef]; nlinarith [exp_one_half_lt_two]
  -- the five estimates
  have hX := tail_prefactor_le_exp hA₀ hG
  have h101 : (101 : ℝ) ^ (4 * n + 4) * (101 : ℝ) ^ (4 * n + 11) ≤
      Real.exp (((8 * n + 15 : ℕ) : ℝ) * 5) := by
    have e : (101 : ℝ) ^ (4 * n + 4) * (101 : ℝ) ^ (4 * n + 11) = (101 : ℝ) ^ (8 * n + 15) := by
      rw [← pow_add]; congr 1; ring
    rw [e, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) e5 _
  have hδ4 : Real.exp (((4 : ℕ) : ℝ) * (-ℓ - 1)) ≤ (δ / 2) ^ 4 := by
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    have hδe : Real.exp (-ℓ) ≤ δ := by
      rw [Real.exp_neg, Real.exp_log ha0]
      rw [div_le_iff₀ hδ] at haδ
      rw [inv_le_iff_one_le_mul₀ ha0]; linarith
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg 1]
    have : (Real.exp 1)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_iff_one_le_mul₀ (Real.exp_pos 1)]; linarith
    nlinarith [Real.exp_pos (-ℓ)]
  have hκ4 : Real.exp (((4 * n : ℕ) : ℝ) * (-(5 * ℓ ^ 2))) ≤ κ ^ (4 * n) := by
    rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (Real.exp_pos _).le hκ _
  have hBQ : B ^ (2 * N₀) * Real.exp (((2 * N₀ : ℕ) : ℝ) * 2) ≤
      (101 : ℝ) ^ (4 * N₀) * U ^ (2 * N₀) := by
    have e : (101 : ℝ) ^ (4 * N₀) * U ^ (2 * N₀) = ((101 : ℝ) ^ 2 * U) ^ (2 * N₀) := by
      rw [mul_pow, ← pow_mul]; ring_nf
    rw [Real.exp_nat_mul, ← mul_pow, e]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.exp_pos 2]
  have hsplit : (1 + 100 : ℝ) ^ (4 * N₀ - 4 * n - 11) * (101 : ℝ) ^ (4 * n + 11) =
      (101 : ℝ) ^ (4 * N₀) := by
    rw [show (1 + 100 : ℝ) = 101 by norm_num, ← pow_add]; congr 1; omega
  -- assembly
  unfold clusterTailConstant clusterFloor
  rw [← hBdef, ← hκdef, ← hUdef, show (100 : ℝ) + 1 = 101 by norm_num,
    show G + 1 + 1 = G + 1 + 1 from rfl]
  have hpos : (0 : ℝ) < 101 ^ (4 * n + 11) := by positivity
  refine lt_of_mul_lt_mul_right ?_ hpos.le
  calc B ^ (2 * N₀) * 101 ^ (4 * n + 4) * (G + 1 + 1) ^ 4 * (24 * A₀ * Real.log (G + 4)) *
        101 ^ (4 * n + 11)
      = B ^ (2 * N₀) * (101 ^ (4 * n + 4) * 101 ^ (4 * n + 11)) *
          ((G + 1 + 1) ^ 4 * (24 * A₀ * Real.log (G + 4))) := by ring
    _ ≤ B ^ (2 * N₀) * Real.exp (((8 * n + 15 : ℕ) : ℝ) * 5) * Real.exp (4 + 5 * Λ) := by
        have : 0 ≤ (G + 1 + 1) ^ 4 * (24 * A₀ * Real.log (G + 4)) := by
          have := Real.log_nonneg (show (1 : ℝ) ≤ G + 4 by linarith)
          have : (0 : ℝ) ≤ A₀ := by linarith
          positivity
        gcongr
    _ = B ^ (2 * N₀) * Real.exp (((8 * n + 15 : ℕ) : ℝ) * 5 + (4 + 5 * Λ)) := by
        rw [mul_assoc, ← Real.exp_add]
    _ < B ^ (2 * N₀) * Real.exp (((2 * N₀ : ℕ) : ℝ) * 2 + ((4 * n : ℕ) : ℝ) * (-(5 * ℓ ^ 2)) +
          ((4 : ℕ) : ℝ) * (-ℓ - 1)) := by
        gcongr
    _ ≤ (101 : ℝ) ^ (4 * N₀) * U ^ (2 * N₀) * κ ^ (4 * n) * (δ / 2) ^ 4 :=
        cluster_horizon_lower hB0 hκ0 hBQ hκ4 hδ4 unitWeightFloor_pos.le
    _ ≤ 79 / 50 * ((1 + 100) ^ (4 * N₀ - 4 * n - 11) * 101 ^ (4 * n + 11)) *
          (U ^ (2 * N₀) * κ ^ (4 * n) * (δ / 2) ^ 4) := by
        rw [hsplit]
        have hX0 : 0 ≤ (101 : ℝ) ^ (4 * N₀) * (U ^ (2 * N₀) * κ ^ (4 * n) * (δ / 2) ^ 4) :=
          mul_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg (mul_nonneg
            (pow_nonneg unitWeightFloor_pos.le _) (pow_nonneg hκ0 _)) (pow_nonneg (by linarith) _))
        calc (101 : ℝ) ^ (4 * N₀) * U ^ (2 * N₀) * κ ^ (4 * n) * (δ / 2) ^ 4
            = 1 * ((101 : ℝ) ^ (4 * N₀) * (U ^ (2 * N₀) * κ ^ (4 * n) * (δ / 2) ^ 4)) := by ring
          _ ≤ 79 / 50 * ((101 : ℝ) ^ (4 * N₀) * (U ^ (2 * N₀) * κ ^ (4 * n) * (δ / 2) ^ 4)) :=
              mul_le_mul_of_nonneg_right (by norm_num) hX0
          _ = _ := by ring
    _ = 79 / 50 * (1 + 100) ^ (4 * N₀ - 4 * n - 11) *
          (U ^ (2 * N₀) * κ ^ (4 * n) * (δ / 2) ^ 4) * 101 ^ (4 * n + 11) := by ring


/-! ### Consequences -/

/-- **Hodge index below the cluster-robust horizon.**  Let `Z` have local count
`N(t, t+1] ≤ A₀ log(|t| + 3)` and let `ρ₀` be a zero with `|β₀ - ½| ≥ δ > 0` and `|γ₀| ≥ 2`.
If at most `n` distinct zeros satisfy `|γ - γ₀| ≤ 101`, and
`a ≥ e⁶`, `a ≥ 1/δ`, `100((n + 1) log² a + log(A₀(|γ₀| + 4))) ≤ a`,
then the level-`a` Hodge index fails. -/
theorem not_hodgeIndex_below_cluster_horizon (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : δ ≤ |ρ₀.re - 1 / 2|)
    (hγ : 2 ≤ |ρ₀.im|) {a : ℝ} (ha6 : Real.exp 6 ≤ a) (haδ : 1 / δ ≤ a) {n : ℕ}
    (hn : Z.Nd (ρ₀.im - 101) (ρ₀.im + 101) ≤ n)
    (hsize : 100 * (((n : ℝ) + 1) * Real.log a ^ 2 + Real.log (A₀ * (|ρ₀.im| + 4))) ≤ a) :
    ¬ HodgeIndexAtLevel Z a := by
  intro hodge
  -- the zero of the pair to the right of the critical line
  obtain ⟨σ, hσ, hσre, hσim⟩ : ∃ σ ∈ Z.carrier, σ.re = 1 / 2 + |ρ₀.re - 1 / 2| ∧
      σ.im = ρ₀.im := by
    rcases le_or_gt (1 / 2) ρ₀.re with h | h
    · exact ⟨ρ₀, hρ₀, by rw [abs_of_nonneg (by linarith)]; ring, rfl⟩
    · refine ⟨reflect ρ₀, Z.reflect_mem ρ₀ hρ₀, ?_, Tail.reflect_im ρ₀⟩
      rw [abs_of_neg (by linarith)]
      simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]; ring
  set δ' := |ρ₀.re - 1 / 2| with hδ'
  have hδ'0 : 0 < δ' := lt_of_lt_of_le hδ hre
  have hst := Z.strip σ hσ
  have hδ'2 : δ' ≤ 1 / 2 := by linarith [hst.2]
  have haδ' : 1 / δ' ≤ a := le_trans (one_div_le_one_div_of_le hδ hre) haδ
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 6) ha6
  obtain ⟨h2n7, hbig⟩ := cluster_horizon_condition hA₀ (abs_nonneg σ.im) hδ'0 hδ'2 ha6 haδ'
    (n := n) (by rw [hσim]; exact hsize)
  have hn' : (Z.finite_window (σ.im - (100 + 1)) (σ.im + (100 + 1))).toFinset.card ≤ n := by
    have e : (Z.finite_window (σ.im - (100 + 1)) (σ.im + (100 + 1))).toFinset.card =
        Z.Nd (σ.im - (100 + 1)) (σ.im + (100 + 1)) :=
      (Set.ncard_eq_toFinset_card (Z.window _ _) (Z.finite_window _ _)).symm
    rw [e, hσim, show (100 : ℝ) + 1 = 101 by norm_num]
    exact hn
  obtain ⟨f, hf, hfs, hp, hm, hneg⟩ := exists_hodge_violation_cluster_robust Z hA₀ hloc hσ hδ'0
    hσre (by rw [hσim]; exact hγ) (H := 100) (by norm_num) (Nat.floor_le ha0.le) hn' h2n7
    (by rw [hσim] at hbig ⊢; exact hbig)
  exact absurd (hodge f hf hfs hp hm) (not_le.mpr hneg)

/-! ### Window counts -/


/-- The number of distinct zeros in `(T, T + m]` is at most the sum of the unit-window counts. -/
theorem Nd_le_sum_unit_N (Z : ZeroConfig) (T : ℝ) :
    ∀ m : ℕ, Z.Nd T (T + m) ≤ ∑ j ∈ Finset.range m, Z.N (T + j) (T + j + 1) := by
  intro m
  induction m with
  | zero =>
    have : Z.window T T = ∅ := by
      ext ρ
      simp only [ZeroConfig.window, Set.mem_inter_iff, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false, not_and, not_le]
      intro _ h; exact h
    simp [ZeroConfig.Nd, this]
  | succ m ih =>
    have hsub : Z.window T (T + ((m + 1 : ℕ) : ℝ)) ⊆
        Z.window T (T + m) ∪ Z.window (T + m) (T + m + 1) := by
      intro ρ hρ
      obtain ⟨hρZ, h1, h2⟩ := hρ
      push_cast at h2
      rcases le_or_gt ρ.im (T + m) with h | h
      · exact Or.inl ⟨hρZ, h1, h⟩
      · exact Or.inr ⟨hρZ, h, by linarith⟩
    have hfin : (Z.window T (T + m) ∪ Z.window (T + m) (T + m + 1)).Finite :=
      (Z.finite_window _ _).union (Z.finite_window _ _)
    have h1 : Z.Nd T (T + ((m + 1 : ℕ) : ℝ)) ≤ Z.Nd T (T + m) + Z.Nd (T + m) (T + m + 1) :=
      (Set.ncard_le_ncard hsub hfin).trans (Set.ncard_union_le _ _)
    rw [Finset.sum_range_succ]
    exact h1.trans (add_le_add ih (Z.Nd_le_N _ _))

/-- The number of distinct zeros in `(T, T + m]` is at most `m A₀ log(|T| + m + 3)`. -/
theorem Nd_le_of_local_count (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (T : ℝ) (m : ℕ) :
    (Z.Nd T (T + m) : ℝ) ≤ m * (A₀ * Real.log (|T| + m + 3)) := by
  have h := Nd_le_sum_unit_N Z T m
  have hA0 : 0 ≤ A₀ := by linarith
  calc (Z.Nd T (T + m) : ℝ) ≤ ∑ j ∈ Finset.range m, (Z.N (T + j) (T + j + 1) : ℝ) := by
        exact_mod_cast h
    _ ≤ ∑ _j ∈ Finset.range m, A₀ * Real.log (|T| + m + 3) := by
        refine Finset.sum_le_sum fun j hj => (hloc _).trans ?_
        have hjm : (j : ℝ) ≤ m := by exact_mod_cast (Finset.mem_range.mp hj).le
        have := abs_add_le T (j : ℝ)
        rw [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) j)] at this
        gcongr
        linarith
    _ = m * (A₀ * Real.log (|T| + m + 3)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The horizon for `ζ`.**  There is `A₀` such that for every `δ > 0`, every zero `ρ` of `ζ`
with `|β - ½| ≥ δ` and `|γ| ≥ 2`, and every level `a ≥ max(e⁶, 1/δ)` with
`10⁵ A₀ log(|γ| + 306) log² a ≤ a`, the level-`a` Hodge index fails.  Equivalently, the Hodge index
at level `a` excludes zeros of depth `δ` up to height `exp(a/(10⁵ A₀ log² a)) - 306`. -/
theorem zeta_hodge_index_cluster_horizon :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ δ : ℝ, 0 < δ → ∀ ρ ∈ zetaZeroConfig.carrier, δ ≤ |ρ.re - 1 / 2| →
      2 ≤ |ρ.im| → ∀ a : ℝ, Real.exp 6 ≤ a → 1 / δ ≤ a →
        10 ^ 5 * A₀ * Real.log (|ρ.im| + 306) * Real.log a ^ 2 ≤ a →
        ¬ HodgeIndexAtLevel zetaZeroConfig a := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨A₀, hA₀, fun δ hδ ρ hρ hre hγ a ha6 haδ hsize => ?_⟩
  set L := Real.log (|ρ.im| + 306) with hL
  set ℓ := Real.log a with hℓ
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 6) ha6
  have hℓ0 : 1 ≤ ℓ := by
    have := Real.log_le_log (Real.exp_pos 6) ha6
    rw [Real.log_exp] at this; linarith
  have hL1 : 1 ≤ L := by
    rw [hL, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    obtain ⟨-, -, -, -, -, -⟩ := exp_numeric_bounds
    have := Real.exp_one_lt_d9
    linarith [abs_nonneg ρ.im]
  have hcount := Nd_le_of_local_count zetaZeroConfig hA₀ hloc (ρ.im - 101) 202
  have hwin : ρ.im - 101 + ((202 : ℕ) : ℝ) = ρ.im + 101 := by push_cast; ring
  rw [hwin] at hcount
  have hcountL : (zetaZeroConfig.Nd (ρ.im - 101) (ρ.im + 101) : ℝ) ≤ 202 * (A₀ * L) := by
    refine hcount.trans ?_
    have hlog : Real.log (|ρ.im - 101| + ((202 : ℕ) : ℝ) + 3) ≤ L := by
      rw [hL]
      apply Real.log_le_log (by positivity)
      have := abs_sub (ρ.im) 101
      push_cast; norm_num at this ⊢; linarith
    have hA0 : 0 ≤ A₀ := by linarith
    push_cast at hlog ⊢
    gcongr
  refine not_hodgeIndex_below_cluster_horizon zetaZeroConfig hA₀ hloc hρ hδ hre hγ ha6 haδ
    (n := zetaZeroConfig.Nd (ρ.im - 101) (ρ.im + 101)) le_rfl ?_
  -- the size condition
  have hA0 : 0 < A₀ := by linarith
  have hlogA : Real.log (A₀ * (|ρ.im| + 4)) ≤ 2 * (A₀ * L) := by
    rw [Real.log_mul hA0.ne' (by positivity)]
    have h1 : Real.log A₀ ≤ A₀ := (Real.log_le_sub_one_of_pos hA0).trans (by linarith)
    have h2 : Real.log (|ρ.im| + 4) ≤ L := Real.log_le_log (by positivity) (by linarith)
    nlinarith
  have hℓ2 : 1 ≤ ℓ ^ 2 := by nlinarith
  have hAL : 1 ≤ A₀ * L := by nlinarith
  set nn := (zetaZeroConfig.Nd (ρ.im - 101) (ρ.im + 101) : ℝ) with hnn
  have hnn0 : 0 ≤ nn := Nat.cast_nonneg _
  have hs1 : (nn + 1) * ℓ ^ 2 ≤ (202 * (A₀ * L) + A₀ * L) * ℓ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hs2 : Real.log (A₀ * (|ρ.im| + 4)) ≤ 2 * (A₀ * L) * ℓ ^ 2 := by nlinarith
  calc 100 * ((nn + 1) * ℓ ^ 2 + Real.log (A₀ * (|ρ.im| + 4)))
      ≤ 100 * ((202 * (A₀ * L) + A₀ * L) * ℓ ^ 2 + 2 * (A₀ * L) * ℓ ^ 2) := by linarith
    _ = 20500 * (A₀ * L) * ℓ ^ 2 := by ring
    _ ≤ 10 ^ 5 * A₀ * L * ℓ ^ 2 := by nlinarith
    _ ≤ a := hsize


/-! ### The Nyquist lattice: the level must be linear in the window count -/

/-- At most `1/h + 1` multiples of `h > 0` lie in an interval `(t, t + 1]`. -/
theorem ncard_latticeWindow_le {h : ℝ} (hh : 0 < h) (t : ℝ) :
    (({k : ℤ | t < (k : ℝ) * h ∧ (k : ℝ) * h ≤ t + 1}.ncard : ℕ) : ℝ) ≤ 1 / h + 1 := by
  set a := ⌊t / h⌋ with ha
  set b := ⌊(t + 1) / h⌋ with hb
  have hsub : {k : ℤ | t < (k : ℝ) * h ∧ (k : ℝ) * h ≤ t + 1} ⊆ (Finset.Ioc a b : Set ℤ) := by
    rintro k ⟨h1, h2⟩
    simp only [Finset.coe_Ioc, Set.mem_Ioc]
    constructor
    · have h3 : t / h < k := by rwa [div_lt_iff₀ hh]
      have h4 : (a : ℝ) < k := (Int.floor_le _).trans_lt h3
      exact_mod_cast h4
    · exact Int.le_floor.mpr (by rwa [le_div_iff₀ hh])
  have hcard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Int.card_Ioc] at hcard
  have hb' : (b : ℝ) ≤ (t + 1) / h := Int.floor_le _
  have ha' : t / h < a + 1 := Int.lt_floor_add_one _
  have hdiff : ((b - a : ℤ) : ℝ) ≤ 1 / h + 1 := by
    push_cast
    have : (t + 1) / h - t / h = 1 / h := by field_simp; ring
    linarith
  have hpos : 0 ≤ 1 / h + 1 := by positivity
  have hc : (({k : ℤ | t < (k : ℝ) * h ∧ (k : ℝ) * h ≤ t + 1}.ncard : ℕ) : ℝ) ≤
      (((b - a).toNat : ℕ) : ℝ) := by exact_mod_cast hcard
  refine hc.trans ?_
  rcases le_or_gt 0 (b - a) with hba | hba
  · have e : (((b - a).toNat : ℕ) : ℝ) = ((b - a : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hba]
    rw [e]; exact hdiff
  · rw [Int.toNat_eq_zero.mpr hba.le]; simpa using hpos

/-- Every unit window of the off-line lattice with spacing `2π/L` carries at most `L/π + 2`
zeros. -/
theorem offLineLatticeConfig_N_le {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (t : ℝ) : ((offLineLatticeConfig hL hδ hδ').N t (t + 1) : ℝ) ≤ L / π + 2 := by
  set Z := offLineLatticeConfig hL hδ hδ' with hZ
  set K := {k : ℤ | t < (k : ℝ) * (2 * π / L) ∧ (k : ℝ) * (2 * π / L) ≤ t + 1} with hK
  have hh : 0 < 2 * π / L := by positivity
  have hKfin : K.Finite := finite_latticeWindow hh t (t + 1)
  have hN : Z.N t (t + 1) = (Z.window t (t + 1)).ncard := by
    unfold ZeroConfig.N
    exact finsum_one
  have hsub : Z.window t (t + 1) ⊆
      verticalLatticePoint L δ '' K ∪ verticalLatticePoint L (-δ) '' K := by
    rintro _ ⟨⟨k, rfl⟩ | ⟨k, rfl⟩, h1, h2⟩
    · exact Or.inl ⟨k, ⟨h1, h2⟩, rfl⟩
    · exact Or.inr ⟨k, ⟨h1, h2⟩, rfl⟩
  have h1 : (Z.window t (t + 1)).ncard ≤ 2 * K.ncard := by
    refine (Set.ncard_le_ncard hsub ((hKfin.image _).union (hKfin.image _))).trans ?_
    refine (Set.ncard_union_le _ _).trans ?_
    have := Set.ncard_image_le (f := verticalLatticePoint L δ) hKfin
    have := Set.ncard_image_le (f := verticalLatticePoint L (-δ)) hKfin
    omega
  have h2 := ncard_latticeWindow_le hh t
  rw [hN]
  have e : 1 / (2 * π / L) = L / (2 * π) := by field_simp
  rw [e] at h2
  calc ((Z.window t (t + 1)).ncard : ℝ) ≤ 2 * (K.ncard : ℝ) := by exact_mod_cast h1
    _ ≤ 2 * (L / (2 * π) + 1) := by gcongr
    _ = L / π + 2 := by field_simp

/-- **The Nyquist lattice masks deep zeros at a level linear in the zero density.**  For
`L ≥ 1` and `0 < δ ≤ ½`, the off-line lattice `{½ ± δ + 2πik/L}`:

* satisfies the local count `N(t, t+1] ≤ (L/π + 2) log(|t| + 3)`;
* has at most `1000 L` distinct zeros in every window of half-width `101`;
* has a zero of depth `δ` above every height;
* satisfies the Hodge index at every level `a ≤ L/2`. -/
theorem offLineLattice_masks_at_linear_level {L δ : ℝ} (hL : 1 ≤ L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) :
    (∀ t : ℝ, ((offLineLatticeConfig (by linarith : (0 : ℝ) < L) hδ hδ').N t (t + 1) : ℝ) ≤
        (L / π + 2) * Real.log (|t| + 3)) ∧
      (∀ γ : ℝ, ((offLineLatticeConfig (by linarith : (0 : ℝ) < L) hδ hδ').Nd
        (γ - 101) (γ + 101) : ℝ) ≤ 1000 * L) ∧
      (∀ T : ℝ, ∃ ρ ∈ (offLineLatticeConfig (by linarith : (0 : ℝ) < L) hδ hδ').carrier,
        ρ.re = 1 / 2 + δ ∧ T ≤ ρ.im) ∧
      ∀ a : ℝ, a ≤ L / 2 →
        HodgeIndexAtLevel (offLineLatticeConfig (by linarith : (0 : ℝ) < L) hδ hδ') a := by
  have hL0 : (0 : ℝ) < L := by linarith
  set Z := offLineLatticeConfig hL0 hδ hδ' with hZ
  have hpi := Real.pi_gt_three
  have hLπ : L / π ≤ L := div_le_self hL0.le (by linarith)
  refine ⟨fun t => ?_, fun γ => ?_, fun T => ?_, fun a ha => ?_⟩
  · have h := offLineLatticeConfig_N_le hL0 hδ hδ' t
    have hlog : 1 ≤ Real.log (|t| + 3) := by
      rw [← Real.log_exp 1]
      apply Real.log_le_log (Real.exp_pos 1)
      have := Real.exp_one_lt_d9
      linarith [abs_nonneg t]
    have : 0 ≤ L / π + 2 := by positivity
    nlinarith
  · have h := Nd_le_sum_unit_N Z (γ - 101) 202
    have hwin : γ - 101 + ((202 : ℕ) : ℝ) = γ + 101 := by push_cast; ring
    rw [hwin] at h
    have hsum : ((∑ j ∈ Finset.range 202, Z.N (γ - 101 + j) (γ - 101 + j + 1) : ℕ) : ℝ) ≤
        202 * (L / π + 2) := by
      push_cast
      calc ∑ j ∈ Finset.range 202, (Z.N (γ - 101 + j) (γ - 101 + j + 1) : ℝ)
          ≤ ∑ _j ∈ Finset.range 202, (L / π + 2) :=
            Finset.sum_le_sum fun j _ => offLineLatticeConfig_N_le hL0 hδ hδ' _
        _ = 202 * (L / π + 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
    calc (Z.Nd (γ - 101) (γ + 101) : ℝ) ≤ _ := by exact_mod_cast h
      _ ≤ 202 * (L / π + 2) := hsum
      _ ≤ 1000 * L := by linarith
  · refine ⟨verticalLatticePoint L δ ⌈T / (2 * π / L)⌉, Or.inl ⟨_, rfl⟩, rfl, ?_⟩
    show T ≤ ((⌈T / (2 * π / L)⌉ : ℤ) : ℝ) * (2 * π / L)
    have hh : 0 < 2 * π / L := by positivity
    rw [← div_le_iff₀ hh]
    exact Int.le_ceil _
  · intro f hf hfs _ _
    exact (offLineLattice_weil_positive_iff hL0 hδ hδ' a).mpr ha f hf hfs

/-- **No exclusion criterion with a sublinear level.**  It is false that the level-`a` Hodge
index fails for every configuration with a zero `ρ` of depth `≥ ¼`, `|γ| ≥ 2`, whenever
`a ≥ e⁶` and the window `|γ' - γ| ≤ 101` holds at most `2000 a` distinct zeros. -/
theorem not_forall_hodge_exclusion_sublinear_level :
    ¬ ∀ (Z : ZeroConfig) (ρ : ℂ), ρ ∈ Z.carrier → 1 / 4 ≤ ρ.re - 1 / 2 → 2 ≤ |ρ.im| →
      ∀ a : ℝ, Real.exp 6 ≤ a →
        (Z.Nd (ρ.im - 101) (ρ.im + 101) : ℝ) ≤ 2000 * a → ¬ HodgeIndexAtLevel Z a := by
  intro H
  set L := 2 * Real.exp 6 with hLdef
  have hL : 1 ≤ L := by
    have := Real.add_one_le_exp 6; rw [hLdef]; linarith
  obtain ⟨-, hcount, hdeep, hhodge⟩ :=
    offLineLattice_masks_at_linear_level hL (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
  obtain ⟨ρ, hρ, hre, hT⟩ := hdeep 2
  have hγ : 2 ≤ |ρ.im| := hT.trans (le_abs_self _)
  refine H _ ρ hρ (by rw [hre]; ring_nf; rfl) hγ (L / 2) (by rw [hLdef]; linarith) ?_
    (hhodge (L / 2) le_rfl)
  calc _ ≤ 1000 * L := hcount ρ.im
    _ = 2000 * (L / 2) := by ring

end RHTower
