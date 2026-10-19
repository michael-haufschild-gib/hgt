import GaloisForLFunctions.SquareRootThreshold.OffLineRunEdgeVisibilityLaw

/-!
# Total-variation blindness of off-line clusters

A **cluster** pushes the double on-line points at finitely many lattice ordinates `2πk/L`,
`k ∈ S`, off the line to depths `d_k ∈ (0, ½]` that may vary from point to point. Extend the depth
profile by `d_k = 0` off `S`; its **total variation** `TV(d) = Σ_k |d_k − d_{k−1}|` counts the
jumps at the two ends of every run as well as the variation inside.

Below the Nyquist aperture (`W_clusterConfig_eq_integral`)

`W(f, f) = 2L‖f‖² + ∫ k(u) Σ_k 2(cosh(d_k u) − 1) e^{2πiku/L} du`.

Summation by parts in `k` (`one_sub_mul_tsum_zpow`) turns the exponential sum into differences of
`cosh(d_k u)`, each at most `|u| sinh(δ|u|) |d_k − d_{k−1}|`, divided by `|1 − e^{2πiu/L}| ≥ 4|u|/L`.
Hence (`re_W_clusterConfig_ge`): for `4a ≤ L` and depths at most `δ`,

`Re W(f, f) ≥ 2L (1 − a · TV(d) · sinh(2δa)) ‖f‖²`.

**The blindness of a cluster depends only on its total depth variation and its maximal depth**,
not on its length, its position or the shape of its profile. A unimodal profile of any length and
shape has `TV(d) = 2δ_max`, so it is invisible exactly where a run of depth `δ_max` is
(`OffLineRunEdgeVisibilityLaw`, the case of constant depth); many small fluctuations add up.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### The cluster configuration -/

/-- The doubled on-line lattice in which each ordinate `2πk/L`, `k ∈ S`, carries the pair
`½ ± d_k + 2πik/L` instead of the double on-line point. -/
def clusterConfig {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (d : ℤ → ℝ) (hd0 : ∀ k ∈ S, 0 < d k)
    (hd1 : ∀ k ∈ S, d k ≤ 1 / 2) : ZeroConfig where
  carrier := ((Set.range fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k) ∪
      Set.range fun k : S => verticalLatticePoint L (d k) k) ∪
    Set.range fun k : S => verticalLatticePoint L (-d k) k
  mult := fun ρ => if ρ.re = 1 / 2 then 2 else 1
  one_le_mult := fun ρ _ => by split_ifs <;> norm_num
  strip := by
    rintro _ ((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩)
    · simp only [verticalLatticePoint]; constructor <;> norm_num
    · simp only [verticalLatticePoint]
      constructor <;> linarith [hd0 k k.2, hd1 k k.2]
    · simp only [verticalLatticePoint]
      constructor <;> linarith [hd0 k k.2, hd1 k k.2]
  reflect_mem := by
    rintro _ ((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩)
    · exact Or.inl (Or.inl ⟨k, by rw [reflect_verticalLatticePoint, neg_zero]⟩)
    · exact Or.inr ⟨k, (reflect_verticalLatticePoint L (d k) k).symm⟩
    · exact Or.inl (Or.inr ⟨k, by rw [reflect_verticalLatticePoint, neg_neg]⟩)
  mult_reflect := by
    intro ρ _
    have hre : (reflect ρ).re = 1 - ρ.re := by simp [reflect]
    simp only [hre]
    by_cases h : ρ.re = 1 / 2
    · rw [if_pos h, if_pos (by linarith)]
    · rw [if_neg h, if_neg (fun h' => h (by linarith))]
  finite_window := by
    intro T₁ T₂
    have hF := finite_latticeWindow (h := 2 * π / L) (by positivity) T₁ T₂
    refine (((hF.image (verticalLatticePoint L 0)).union
      (hF.image fun k => verticalLatticePoint L (d k) k)).union
        (hF.image fun k => verticalLatticePoint L (-d k) k)).subset ?_
    rintro _ ⟨((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩), h1, h2⟩
    · exact Or.inl (Or.inl ⟨k, ⟨h1, h2⟩, rfl⟩)
    · exact Or.inl (Or.inr ⟨k, ⟨h1, h2⟩, rfl⟩)
    · exact Or.inr ⟨k, ⟨h1, h2⟩, rfl⟩

/-- Lattice points with the same index are equal only for equal depths; different indices give
different points. -/
theorem verticalLatticePoint_index_eq {L : ℝ} (hL : 0 < L) {δ₁ δ₂ : ℝ} {k k' : ℤ}
    (h : verticalLatticePoint L δ₁ k = verticalLatticePoint L δ₂ k') : k = k' := by
  have him := congrArg Complex.im h
  simp only [verticalLatticePoint] at him
  have hh : (2 * π / L) ≠ 0 := by positivity
  exact_mod_cast mul_right_cancel₀ hh him

/-- Below the Nyquist aperture the cluster configuration has Weil form `2L‖f‖²` plus, for each
`k ∈ S`, the pair summands minus the removed double on-line summand. -/
theorem W_clusterConfig {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (d : ℤ → ℝ)
    (hd0 : ∀ k ∈ S, 0 < d k) (hd1 : ∀ k ∈ S, d k ≤ 1 / 2)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) :
    (clusterConfig hL S d hd0 hd1).W f f = 2 * L * (∫ t, f t * conj (f t)) +
      ∑ k ∈ S, (paperFT (EF.weilTest f f) ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) - I * d k) +
        paperFT (EF.weilTest f f) ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) + I * d k) -
        2 * paperFT (EF.weilTest f f) (((k : ℝ) * (2 * π / L) : ℝ) : ℂ)) := by
  set Z := clusterConfig hL S d hd0 hd1 with hZ
  set K := EF.weilTest f f with hKdef
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hK := EF.weilTest_contDiff hf hf.continuous hfc
  have hKs := weilTest_abs_le hfs hfs
  have hmultdef : ∀ ρ, Z.mult ρ = if ρ.re = 1 / 2 then 2 else 1 := fun _ => rfl
  have hs0 : ∀ k : ℤ, Z.Wsummand f f (verticalLatticePoint L 0 k) =
      2 * paperFT K (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) := by
    intro k
    rw [Wsummand_verticalLatticePoint _ hf.continuous hf.continuous hfc hfc, hmultdef,
      if_pos (by simp [verticalLatticePoint])]
    simp [hKdef]
  have hsp : ∀ k : S, Z.Wsummand f f (verticalLatticePoint L (d k) k) =
      paperFT K ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) - I * d k) := by
    intro k
    have := hd0 k k.2
    rw [Wsummand_verticalLatticePoint _ hf.continuous hf.continuous hfc hfc, hmultdef,
      if_neg (by simp only [verticalLatticePoint]; linarith)]
    simp [hKdef]
  have hsm : ∀ k : S, Z.Wsummand f f (verticalLatticePoint L (-d k) k) =
      paperFT K ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) + I * d k) := by
    intro k
    have := hd0 k k.2
    rw [Wsummand_verticalLatticePoint _ hf.continuous hf.continuous hfc hfc, hmultdef,
      if_neg (by simp only [verticalLatticePoint]; linarith)]
    push_cast
    rw [show ((k : ℂ) * (2 * π / L)) - I * -(d k : ℂ) = (k : ℂ) * (2 * π / L) + I * d k by ring]
    simp [hKdef]
  -- the full doubled lattice
  have hfull : HasSum (fun k : ℤ => 2 * paperFT K (((k : ℝ) * (2 * π / L) : ℝ) : ℂ))
      (2 * L * ∫ t, f t * conj (f t)) := by
    have h0 := tsum_weilTest_lattice_eq hL hf hf.continuous hfs hfs
      (fun m : ℤ => (Real.exp (0 * (m * L)) : ℂ)) (by simp)
    have h2 := (hasSum_paperFT_lattice_sub_I_mul hL hK hKs 0).mul_left 2
    rw [h0] at h2
    have hfun : (fun k : ℤ => 2 * paperFT K (((k : ℝ) * (2 * π / L) : ℝ) : ℂ)) =
        fun i : ℤ => 2 * paperFT (EF.weilTest f f)
          ((((i : ℝ) * (2 * π / L) : ℝ) : ℂ) - I * ((0 : ℝ) : ℂ)) := by
      funext k
      simp [hKdef]
    rw [hfun, show (2 * (L : ℂ) * ∫ t, f t * conj (f t)) = 2 * (L * ∫ t, f t * conj (f t)) by
      ring]
    exact h2
  have hA : HasSum (fun ρ : Set.range (fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k) =>
      Z.Wsummand f f ρ) (2 * L * (∫ t, f t * conj (f t)) -
        ∑ k ∈ S, 2 * paperFT K (((k : ℝ) * (2 * π / L) : ℝ) : ℂ)) := by
    have hinj : Function.Injective (fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k) :=
      fun k k' h => Subtype.ext (verticalLatticePoint_injective hL 0 h)
    rw [hinj.hasSum_range_iff]
    have := (Finset.hasSum_compl_iff
      (f := fun k : ℤ => 2 * paperFT K (((k : ℝ) * (2 * π / L) : ℝ) : ℂ)) S).mpr
      (by rwa [sub_add_cancel])
    have hfun : (Z.Wsummand f f ∘ fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k) =
        fun x : {k : ℤ // k ∉ S} => 2 * paperFT K ((((x : ℤ) : ℝ) * (2 * π / L) : ℝ) : ℂ) :=
      funext fun k => hs0 k
    rw [hfun]
    exact this
  have hBp : HasSum (fun ρ : Set.range (fun k : S => verticalLatticePoint L (d k) k) =>
      Z.Wsummand f f ρ) (∑ k : S, Z.Wsummand f f (verticalLatticePoint L (d k) k)) := by
    have hinj : Function.Injective (fun k : S => verticalLatticePoint L (d k) k) :=
      fun k k' h => Subtype.ext (verticalLatticePoint_index_eq hL h)
    rw [hinj.hasSum_range_iff]
    exact hasSum_fintype _
  have hBm : HasSum (fun ρ : Set.range (fun k : S => verticalLatticePoint L (-d k) k) =>
      Z.Wsummand f f ρ) (∑ k : S, Z.Wsummand f f (verticalLatticePoint L (-d k) k)) := by
    have hinj : Function.Injective (fun k : S => verticalLatticePoint L (-d k) k) :=
      fun k k' h => Subtype.ext (verticalLatticePoint_index_eq hL h)
    rw [hinj.hasSum_range_iff]
    exact hasSum_fintype _
  have hd₁ : Disjoint (Set.range fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k)
      (Set.range fun k : S => verticalLatticePoint L (d k) k) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ ⟨k', hk'⟩
    have := congrArg Complex.re hk'
    simp only [verticalLatticePoint] at this
    linarith [hd0 k' k'.2]
  have hd₂ : Disjoint ((Set.range fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k) ∪
      Set.range fun k : S => verticalLatticePoint L (d k) k)
      (Set.range fun k : S => verticalLatticePoint L (-d k) k) := by
    rw [Set.disjoint_left]
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩) ⟨k', hk'⟩
    · have := congrArg Complex.re hk'
      simp only [verticalLatticePoint] at this
      linarith [hd0 k' k'.2]
    · have := congrArg Complex.re hk'
      simp only [verticalLatticePoint] at this
      linarith [hd0 k' k'.2, hd0 k k.2]
  have hall := HasSum.add_disjoint (f := Z.Wsummand f f) hd₂
    (HasSum.add_disjoint (f := Z.Wsummand f f) hd₁ hA hBp) hBm
  have heq := hall.tsum_eq
  rw [ZeroConfig.W]
  refine heq.trans ?_
  simp only [hsp, hsm]
  rw [← Finset.sum_coe_sort S (fun k => paperFT K _ + paperFT K _ - 2 * paperFT K _),
    ← Finset.sum_coe_sort S (fun k => 2 * paperFT K _)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- **The cluster formula.** Below the Nyquist aperture,
`W(f, f) = 2L‖f‖² + ∫ k(u) Σ_{k ∈ S} 2(cosh(d_k u) − 1) e^{2πiku/L} du`. -/
theorem W_clusterConfig_eq_integral {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (d : ℤ → ℝ)
    (hd0 : ∀ k ∈ S, 0 < d k) (hd1 : ∀ k ∈ S, d k ≤ 1 / 2) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) :
    (clusterConfig hL S d hd0 hd1).W f f = 2 * L * (∫ t, f t * conj (f t)) +
      ∫ u, EF.weilTest f f u * ∑ k ∈ S, ((2 * (Real.cosh (d k * u) - 1) : ℝ) : ℂ) *
        cexp (I * (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) * u) := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hK := (EF.weilTest_contDiff hf hf.continuous hfc).continuous
  have hKc : HasCompactSupport (EF.weilTest f f) :=
    hasCompactSupport_of_tsupport_subset_Icc (EF.tsupport_weilTest_subset hfs hfs)
  rw [W_clusterConfig hL S d hd0 hd1 hf hfs]
  congr 1
  simp_rw [paperFT_pair_sub_double hK hKc, Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    congr 1 with u
    ring
  · intro k _
    exact integrable_mul_of_hasCompactSupport hK hKc (by fun_prop)


/-! ### Summation by parts along the lattice -/

/-- **Summation by parts.** For a finitely supported sequence `c` and `z ≠ 0`,
`(1 − z) Σ_k c_k z^k = Σ_k (c_k − c_{k−1}) z^k`. -/
theorem one_sub_mul_tsum_zpow {c : ℤ → ℂ} {T : Finset ℤ} (hc : ∀ k ∉ T, c k = 0) {z : ℂ}
    (hz : z ≠ 0) :
    (1 - z) * ∑' k : ℤ, c k * z ^ k = ∑' k : ℤ, (c k - c (k - 1)) * z ^ k := by
  have hs1 : Summable fun k : ℤ => c k * z ^ k :=
    summable_of_ne_finset_zero (s := T) fun k hk => by rw [hc k hk, zero_mul]
  have hs2 : Summable fun k : ℤ => c (k - 1) * z ^ k :=
    summable_of_ne_finset_zero (s := T.map (Equiv.addRight 1).toEmbedding) fun k hk => by
      rw [hc (k - 1) fun h => hk (Finset.mem_map.mpr ⟨k - 1, h, by simp⟩), zero_mul]
  have hshift : ∑' k : ℤ, c (k - 1) * z ^ k = z * ∑' k : ℤ, c k * z ^ k := by
    rw [← (Equiv.addRight (1 : ℤ)).tsum_eq, ← tsum_mul_left]
    congr 1 with k
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    rw [zpow_add₀ hz, zpow_one]
    ring
  have hsplit : ∑' k : ℤ, (c k - c (k - 1)) * z ^ k =
      ∑' k : ℤ, c k * z ^ k - ∑' k : ℤ, c (k - 1) * z ^ k := by
    rw [← Summable.tsum_sub hs1 hs2]
    congr 1 with k
    ring
  rw [hsplit, hshift]
  ring

/-- `|cosh x − cosh y| ≤ sinh M · |x − y|` for `|x|, |y| ≤ M`. -/
theorem abs_cosh_sub_cosh_le {x y M : ℝ} (hx : |x| ≤ M) (hy : |y| ≤ M) :
    |Real.cosh x - Real.cosh y| ≤ Real.sinh M * |x - y| := by
  have key : ∀ {p q : ℝ}, p < q → |p| ≤ M → |q| ≤ M →
      |Real.cosh q - Real.cosh p| ≤ Real.sinh M * (q - p) := by
    intro p q hpq hp hq
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Real.cosh Real.sinh hpq
      Real.continuous_cosh.continuousOn fun z _ => Real.hasDerivAt_cosh z
    rw [eq_div_iff (by linarith)] at hcd
    rw [← hcd, abs_mul, abs_of_pos (by linarith : 0 < q - p)]
    gcongr
    have hcM : |c| ≤ M := abs_le.mpr ⟨by linarith [(abs_le.mp hp).1, hc.1],
      by linarith [(abs_le.mp hq).2, hc.2]⟩
    rw [Real.abs_sinh]
    exact Real.sinh_le_sinh.mpr hcM
  rcases lt_trichotomy x y with h | h | h
  · rw [abs_sub_comm, abs_sub_comm x y, abs_of_pos (by linarith : 0 < y - x)]
    exact key h hx hy
  · subst h; simp
  · rw [abs_of_pos (by linarith : 0 < x - y)]
    exact key h hy hx

/-! ### Total-variation blindness -/

/-- The depth profile extended by `0` off the cluster. -/
def zeroExt (S : Finset ℤ) (d : ℤ → ℝ) (k : ℤ) : ℝ := if k ∈ S then d k else 0

/-- The total variation `Σ_k |d_k − d_{k−1}|` of the zero-extended depth profile. -/
def depthVariation (S : Finset ℤ) (d : ℤ → ℝ) : ℝ :=
  ∑' k : ℤ, |zeroExt S d k - zeroExt S d (k - 1)|

theorem zeroExt_eq_zero {S : Finset ℤ} {d : ℤ → ℝ} {k : ℤ} (hk : k ∉ S) : zeroExt S d k = 0 := by
  simp [zeroExt, hk]

theorem summable_depthVariation (S : Finset ℤ) (d : ℤ → ℝ) :
    Summable fun k : ℤ => |zeroExt S d k - zeroExt S d (k - 1)| :=
  summable_of_ne_finset_zero (s := S ∪ S.map (Equiv.addRight 1).toEmbedding) fun k hk => by
    rw [Finset.mem_union, not_or] at hk
    rw [zeroExt_eq_zero hk.1, zeroExt_eq_zero fun h => hk.2 (Finset.mem_map.mpr
      ⟨k - 1, h, by simp⟩), sub_zero, abs_zero]

/-- **Exponential sums of a cluster.** For `0 < |u| ≤ L/2` and depths in `[0, δ]`,
`|Σ_{k ∈ S} 2(cosh(d_k u) − 1) e^{2πiku/L}| ≤ (L/2) TV(d) sinh(δ|u|)`. -/
theorem norm_cluster_sum_le {L u δ : ℝ} (hL : 0 < L) (hu : u ≠ 0) (huL : |u| ≤ L / 2)
    (S : Finset ℤ) (d : ℤ → ℝ) (hδ : 0 ≤ δ) (hd0 : ∀ k ∈ S, 0 ≤ d k) (hdδ : ∀ k ∈ S, d k ≤ δ) :
    ‖∑ k ∈ S, ((2 * (Real.cosh (d k * u) - 1) : ℝ) : ℂ) *
        cexp (I * (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) * u)‖ ≤
      L / 2 * depthVariation S d * Real.sinh (δ * |u|) := by
  set z : ℂ := cexp (I * ((2 * π / L * u : ℝ) : ℂ)) with hz
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hlow := four_mul_abs_div_le_norm_cexp_sub_one hL huL
  rw [← hz] at hlow
  have hu' : 0 < |u| := abs_pos.mpr hu
  have hlowpos : 0 < 4 * |u| / L := by positivity
  set c : ℤ → ℂ := fun k => ((2 * (Real.cosh (zeroExt S d k * u) - 1) : ℝ) : ℂ) with hc
  have hcz : ∀ k ∉ S, c k = 0 := by
    intro k hk; simp [hc, zeroExt_eq_zero hk]
  have hsum : ∑ k ∈ S, ((2 * (Real.cosh (d k * u) - 1) : ℝ) : ℂ) *
      cexp (I * (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) * u) = ∑' k : ℤ, c k * z ^ k := by
    rw [tsum_eq_sum (s := S) fun k hk => by rw [hcz k hk, zero_mul]]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hc, hz, ← Complex.exp_int_mul]
    simp only [zeroExt, if_pos hk]
    congr 2
    push_cast
    ring
  rw [hsum]
  have habel := one_sub_mul_tsum_zpow hcz hz0
  have h1z : (1 - z) ≠ 0 := by
    intro h
    have hz1 : z = 1 := (sub_eq_zero.mp h).symm
    rw [hz1, sub_self, norm_zero] at hlow
    linarith
  -- each difference is controlled by the depth difference
  have hext : ∀ j : ℤ, |zeroExt S d j * u| ≤ δ * |u| := by
    intro j
    rw [abs_mul]
    gcongr
    by_cases hj : j ∈ S
    · simp only [zeroExt, if_pos hj]
      rw [abs_of_nonneg (hd0 j hj)]; exact hdδ j hj
    · simp only [zeroExt, if_neg hj, abs_zero]
      exact hδ
  have hdiff : ∀ k : ℤ, ‖c k - c (k - 1)‖ ≤
      2 * |u| * Real.sinh (δ * |u|) * |zeroExt S d k - zeroExt S d (k - 1)| := by
    intro k
    rw [hc]
    simp only
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      show 2 * (Real.cosh (zeroExt S d k * u) - 1) - 2 * (Real.cosh (zeroExt S d (k - 1) * u) - 1)
        = 2 * (Real.cosh (zeroExt S d k * u) - Real.cosh (zeroExt S d (k - 1) * u)) by ring,
      abs_mul, abs_two]
    have := abs_cosh_sub_cosh_le (hext k) (hext (k - 1))
    rw [← sub_mul, abs_mul] at this
    calc 2 * |Real.cosh (zeroExt S d k * u) - Real.cosh (zeroExt S d (k - 1) * u)|
        ≤ 2 * (Real.sinh (δ * |u|) * (|zeroExt S d k - zeroExt S d (k - 1)| * |u|)) := by
          gcongr
      _ = 2 * |u| * Real.sinh (δ * |u|) * |zeroExt S d k - zeroExt S d (k - 1)| := by ring
  -- finite supports
  set T : Finset ℤ := S ∪ S.map (Equiv.addRight 1).toEmbedding with hT
  have hΔz : ∀ k ∉ T, c k - c (k - 1) = 0 := by
    intro k hk
    rw [hT, Finset.mem_union, not_or] at hk
    rw [hcz k hk.1, hcz (k - 1) fun h => hk.2 (Finset.mem_map.mpr ⟨k - 1, h, by simp⟩), sub_zero]
  have hzn : ‖z‖ = 1 := by rw [hz, mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hs1 : Summable fun k : ℤ => ‖(c k - c (k - 1)) * z ^ k‖ :=
    summable_of_ne_finset_zero (s := T) fun k hk => by rw [hΔz k hk, zero_mul, norm_zero]
  have hs2 : Summable fun k : ℤ => 2 * |u| * Real.sinh (δ * |u|) *
      |zeroExt S d k - zeroExt S d (k - 1)| := (summable_depthVariation S d).mul_left _
  have hnorm : ‖∑' k : ℤ, c k * z ^ k‖ =
      ‖∑' k : ℤ, (c k - c (k - 1)) * z ^ k‖ / ‖1 - z‖ := by
    rw [← habel, norm_mul, mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr h1z)]
  have hnum : ‖∑' k : ℤ, (c k - c (k - 1)) * z ^ k‖ ≤
      2 * |u| * Real.sinh (δ * |u|) * depthVariation S d := by
    refine (norm_tsum_le_tsum_norm hs1).trans ?_
    rw [depthVariation, ← tsum_mul_left]
    refine hs1.tsum_le_tsum (fun k => ?_) hs2
    rw [norm_mul, norm_zpow, hzn, one_zpow, mul_one]
    exact hdiff k
  rw [hnorm, div_le_iff₀ (lt_of_lt_of_le hlowpos (by rw [norm_sub_rev]; exact hlow))]
  have hsh : 0 ≤ Real.sinh (δ * |u|) := Real.sinh_nonneg_iff.mpr (by positivity)
  have hTV : 0 ≤ depthVariation S d := tsum_nonneg fun k => abs_nonneg _
  calc ‖∑' k : ℤ, (c k - c (k - 1)) * z ^ k‖
      ≤ 2 * |u| * Real.sinh (δ * |u|) * depthVariation S d := hnum
    _ = L / 2 * depthVariation S d * Real.sinh (δ * |u|) * (4 * |u| / L) := by field_simp; ring
    _ ≤ L / 2 * depthVariation S d * Real.sinh (δ * |u|) * ‖1 - z‖ := by
        gcongr
        rw [norm_sub_rev]; exact hlow

/-- **Total-variation blindness.** For `4a ≤ L` and depths in `(0, δ]`, every cluster satisfies
`Re W(f, f) ≥ 2L (1 − a · TV(d) · sinh(2δa)) ‖f‖²` on tests supported in `[-a, a]`. -/
theorem re_W_clusterConfig_ge {L δ a : ℝ} (hL : 0 < L) (S : Finset ℤ) (d : ℤ → ℝ)
    (hd0 : ∀ k ∈ S, 0 < d k) (hd1 : ∀ k ∈ S, d k ≤ 1 / 2) (hdδ : ∀ k ∈ S, d k ≤ δ) (hδ : 0 ≤ δ)
    (ha : 0 ≤ a) (haL : 4 * a ≤ L) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    2 * L * (1 - a * depthVariation S d * Real.sinh (2 * δ * a)) * ∫ t, ‖f t‖ ^ 2 ≤
      ((clusterConfig hL S d hd0 hd1).W f f).re := by
  have hfs' : tsupport f ⊆ Icc (-(L / 2)) (L / 2) :=
    hfs.trans (Icc_subset_Icc (by linarith) (by linarith))
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hKs : tsupport (EF.weilTest f f) ⊆ Icc (-(2 * a)) (2 * a) :=
    EF.tsupport_weilTest_subset (L := 2 * a) (by rwa [show 2 * a / 2 = a by ring])
      (by rwa [show 2 * a / 2 = a by ring])
  have hE0 : 0 ≤ ∫ t, ‖f t‖ ^ 2 := integral_nonneg fun t => by positivity
  have hTV : 0 ≤ depthVariation S d := tsum_nonneg fun k => abs_nonneg _
  have hsh : 0 ≤ Real.sinh (2 * δ * a) := Real.sinh_nonneg_iff.mpr (by positivity)
  rw [W_clusterConfig_eq_integral hL S d hd0 hd1 hf hfs', integral_mul_conj_self_eq,
    Complex.add_re]
  set F : ℝ → ℂ := fun u => EF.weilTest f f u * ∑ k ∈ S,
    ((2 * (Real.cosh (d k * u) - 1) : ℝ) : ℂ) *
      cexp (I * (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) * u) with hF
  have hFz : ∀ u, u ∉ Icc (-(2 * a)) (2 * a) → F u = 0 := by
    intro u hu
    rw [hF]
    simp only
    rw [image_eq_zero_of_notMem_tsupport (fun h => hu (hKs h)), zero_mul]
  have hFn : ∀ u ∈ Icc (-(2 * a)) (2 * a), ‖F u‖ ≤
      (∫ t, ‖f t‖ ^ 2) * (L / 2 * depthVariation S d * Real.sinh (2 * δ * a)) := by
    intro u hu
    have hu' : |u| ≤ 2 * a := abs_le.mpr ⟨hu.1, hu.2⟩
    rcases eq_or_ne u 0 with h0 | h0
    · subst h0
      have : F 0 = 0 := by
        rw [hF]; simp
      rw [this, norm_zero]; positivity
    rw [hF, norm_mul]
    refine mul_le_mul (norm_weilTest_self_le hf.continuous hfc u) ?_ (norm_nonneg _) hE0
    refine (norm_cluster_sum_le hL h0 (by linarith) S d hδ (fun k hk => (hd0 k hk).le) hdδ).trans ?_
    gcongr
    exact Real.sinh_le_sinh.mpr (by nlinarith)
  have hbound : ‖∫ u, F u‖ ≤ (∫ t, ‖f t‖ ^ 2) *
      (L / 2 * depthVariation S d * Real.sinh (2 * δ * a)) * (4 * a) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hFz]
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (-(2 * a)) (2 * a))
      (f := F) (by simp) hFn
    rwa [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
      show 2 * a - -(2 * a) = 4 * a by ring] at this
  have hre : -‖∫ u, F u‖ ≤ (∫ u, F u).re := by
    have := Complex.abs_re_le_norm (∫ u, F u)
    linarith [neg_abs_le (∫ u, F u).re]
  rw [show ((2 : ℂ) * L * ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ)).re = 2 * L * ∫ t, ‖f t‖ ^ 2 by
    rw [show ((2 : ℂ) * L * ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ)) = ((2 * L * ∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]]
  nlinarith

/-- **Clusters of small total variation are invisible.** If `a · TV(d) · sinh(2δa) ≤ 1` and
`4a ≤ L`, the cluster is Weil-nonnegative on all tests supported in `[-a, a]`, whatever its
length, position and the shape of its depth profile. -/
theorem re_W_clusterConfig_nonneg {L δ a : ℝ} (hL : 0 < L) (S : Finset ℤ) (d : ℤ → ℝ)
    (hd0 : ∀ k ∈ S, 0 < d k) (hd1 : ∀ k ∈ S, d k ≤ 1 / 2) (hdδ : ∀ k ∈ S, d k ≤ δ) (hδ : 0 ≤ δ)
    (ha : 0 ≤ a) (haL : 4 * a ≤ L) (hTV : a * depthVariation S d * Real.sinh (2 * δ * a) ≤ 1)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    0 ≤ ((clusterConfig hL S d hd0 hd1).W f f).re := by
  refine le_trans ?_ (re_W_clusterConfig_ge hL S d hd0 hd1 hdδ hδ ha haL hf hfs)
  have : 0 ≤ ∫ t, ‖f t‖ ^ 2 := integral_nonneg fun t => by positivity
  have : 0 ≤ 1 - a * depthVariation S d * Real.sinh (2 * δ * a) := by linarith
  positivity

/-- A run of constant depth `δ` has total variation `2δ`: one jump up, one jump down. -/
theorem depthVariation_runSet_const (k₀ : ℤ) {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 ≤ δ) :
    depthVariation (runSet k₀ N) (fun _ => δ) = 2 * δ := by
  have hmem : ∀ k : ℤ, k ∈ runSet k₀ N ↔ k₀ ≤ k ∧ k < k₀ + N := by
    intro k
    simp only [runSet, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨j, hj, rfl⟩; omega
    · intro h; exact ⟨(k - k₀).toNat, by omega, by omega⟩
  have hk₀ : k₀ ≠ k₀ + N := by omega
  rw [depthVariation, tsum_eq_sum (s := {k₀, k₀ + N}) fun k hk => ?_, Finset.sum_pair hk₀]
  · simp only [zeroExt, hmem]
    have h1 : ¬ (k₀ ≤ k₀ - 1 ∧ k₀ - 1 < k₀ + N) := by omega
    have h2 : (k₀ ≤ k₀ ∧ k₀ < k₀ + N) := by omega
    have h3 : ¬ (k₀ ≤ k₀ + N ∧ k₀ + N < k₀ + N) := by omega
    have h4 : (k₀ ≤ k₀ + N - 1 ∧ k₀ + N - 1 < k₀ + N) := by omega
    rw [if_pos h2, if_neg h1, if_neg h3, if_pos h4, sub_zero, zero_sub, abs_neg,
      abs_of_nonneg hδ]
    ring
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    simp only [zeroExt, hmem]
    by_cases h : k₀ ≤ k ∧ k < k₀ + N
    · have h' : k₀ ≤ k - 1 ∧ k - 1 < k₀ + N := by omega
      rw [if_pos h, if_pos h', sub_self, abs_zero]
    · have h' : ¬ (k₀ ≤ k - 1 ∧ k - 1 < k₀ + N) := by omega
      rw [if_neg h, if_neg h', sub_self, abs_zero]

end GaloisForLFunctions.SquareRootThreshold
