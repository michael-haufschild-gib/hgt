import Mathlib
import GaloisForLFunctions.RHTower.LargeValues

/-!
# Extracting a well-spaced subset from a locally bounded finite set

A large-values inequality for Dirichlet polynomials counts points that are `δ`-separated, but the
points one wants to feed it — the ordinates of zeta zeros in a box — are not separated.  What is
available instead is a *local* bound: every window of length `δ` contains at most `K` of them.

Bucketing by `⌊x/δ⌋` turns the local bound into a global one.  Each bucket holds at most `K` points,
so at least `|S|/K` buckets are occupied; taking one representative from every occupied bucket of a
fixed parity gives indices differing by at least `2`, hence points differing by at least `δ`.
Choosing the better parity costs a further factor `2`:

```text
|S| ≤ 2·K·|P| ,      P ⊆ S ,      x ≠ z in P ⟹ δ ≤ |x − z| .
```

The factor `2K` is the source of the logarithmic loss in classical density estimates, where
`K = O(log T)` by the local Riemann–von Mangoldt zero count.
-/

open Finset

namespace RHTower

/-- The bucket index of a real number at scale `δ`. -/
noncomputable def bucket (δ x : ℝ) : ℤ := ⌊x / δ⌋

/-- A point lies in the half-open interval indexed by its bucket. -/
theorem bucket_mem_Ico {δ x : ℝ} (hδ : 0 < δ) :
    (bucket δ x : ℝ) * δ ≤ x ∧ x < ((bucket δ x : ℝ) + 1) * δ := by
  unfold bucket
  constructor
  · have h := Int.floor_le (x / δ)
    have hx : (⌊x / δ⌋ : ℝ) * δ ≤ (x / δ) * δ := by nlinarith
    calc (⌊x / δ⌋ : ℝ) * δ ≤ (x / δ) * δ := hx
      _ = x := by field_simp
  · have h := Int.lt_floor_add_one (x / δ)
    have hx : (x / δ) * δ < ((⌊x / δ⌋ : ℝ) + 1) * δ := by nlinarith
    calc x = (x / δ) * δ := by field_simp
      _ < ((⌊x / δ⌋ : ℝ) + 1) * δ := hx

/-- Points whose bucket indices differ by at least `2` are at distance at least `δ`. -/
theorem delta_le_dist_of_two_le_abs_bucket_sub {δ x z : ℝ} (hδ : 0 < δ)
    (h : 2 ≤ |bucket δ x - bucket δ z|) : δ ≤ |x - z| := by
  have key : ∀ u v : ℝ, bucket δ u + 2 ≤ bucket δ v → δ ≤ |u - v| := by
    intro u v huv
    obtain ⟨-, hu2⟩ := bucket_mem_Ico (δ := δ) (x := u) hδ
    obtain ⟨hv1, -⟩ := bucket_mem_Ico (δ := δ) (x := v) hδ
    have hcast : (bucket δ u : ℝ) + 2 ≤ (bucket δ v : ℝ) := by exact_mod_cast huv
    have huv' : u < v := by nlinarith
    rw [abs_sub_comm, abs_of_pos (by linarith : (0 : ℝ) < v - u)]
    nlinarith
  rcases le_total (bucket δ x) (bucket δ z) with hle | hle
  · have : bucket δ x + 2 ≤ bucket δ z := by
      rw [abs_of_nonpos (by omega)] at h; omega
    exact key x z this
  · have : bucket δ z + 2 ≤ bucket δ x := by
      rw [abs_of_nonneg (by omega)] at h; omega
    rw [abs_sub_comm]
    exact key z x this

/-- Two distinct integers of the same parity differ by at least `2`. -/
theorem two_le_abs_sub_of_even_sub {m n : ℤ} (hpar : Even (m - n)) (hne : m ≠ n) :
    2 ≤ |m - n| := by
  obtain ⟨k, hk⟩ := hpar
  have hk0 : k ≠ 0 := by
    intro h
    apply hne
    omega
  have h1 : 1 ≤ |k| := by
    rcases lt_or_gt_of_ne hk0 with h | h
    · rw [abs_of_neg h]; omega
    · rw [abs_of_pos h]; omega
  have : |m - n| = 2 * |k| := by
    rw [hk, show k + k = 2 * k by ring, abs_mul]
    norm_num
  omega

/-- **Well-spaced extraction.**  If every bucket of scale `δ` meets the finite set `S` in at most `K`
points, then `S` has a `δ`-separated subset `P` with `|S| ≤ 2K·|P|`. -/
theorem exists_wellSpaced_subset {δ : ℝ} (hδ : 0 < δ) {K : ℕ} (S : Finset ℝ)
    (hloc : ∀ n : ℤ, (S.filter fun x => bucket δ x = n).card ≤ K) :
    ∃ P : Finset ℝ, P ⊆ S ∧ S.card ≤ 2 * K * P.card ∧
      ∀ x ∈ P, ∀ z ∈ P, x ≠ z → δ ≤ |x - z| := by
  classical
  set G : Finset ℤ := S.image (bucket δ) with hGdef
  have hcardS : S.card ≤ K * G.card := by
    have hfib : S.card = ∑ n ∈ G, (S.filter fun x => bucket δ x = n).card :=
      Finset.card_eq_sum_card_fiberwise fun x hx => Finset.mem_image_of_mem _ hx
    calc S.card = ∑ n ∈ G, (S.filter fun x => bucket δ x = n).card := hfib
      _ ≤ ∑ _n ∈ G, K := Finset.sum_le_sum fun n _ => hloc n
      _ = K * G.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hrep : ∀ n : ℤ, ∃ x : ℝ, n ∈ G → (x ∈ S ∧ bucket δ x = n) := by
    intro n
    by_cases hn : n ∈ G
    · rw [hGdef, Finset.mem_image] at hn
      obtain ⟨x, hx, hxn⟩ := hn
      exact ⟨x, fun _ => ⟨hx, hxn⟩⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose f hf using hrep
  -- for a parity-homogeneous family of buckets the representatives are `δ`-separated
  have hbuild : ∀ H : Finset ℤ, H ⊆ G → (∀ m ∈ H, ∀ n ∈ H, Even (m - n)) →
      ∃ P : Finset ℝ, P ⊆ S ∧ H.card ≤ P.card ∧
        ∀ x ∈ P, ∀ z ∈ P, x ≠ z → δ ≤ |x - z| := by
    intro H hHG hpar
    refine ⟨H.image f, ?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨n, hn, rfl⟩ := hx
      exact (hf n (hHG hn)).1
    · have hinj : Set.InjOn f ↑H := by
        intro m hm n hn hfe
        have hbm := (hf m (hHG (Finset.mem_coe.mp hm))).2
        have hbn := (hf n (hHG (Finset.mem_coe.mp hn))).2
        rw [← hbm, ← hbn, hfe]
      rw [Finset.card_image_of_injOn hinj]
    · intro x hx z hz hxz
      rw [Finset.mem_image] at hx hz
      obtain ⟨m, hm, rfl⟩ := hx
      obtain ⟨n, hn, rfl⟩ := hz
      have hbm := (hf m (hHG hm)).2
      have hbn := (hf n (hHG hn)).2
      have hmn : m ≠ n := by
        intro h
        exact hxz (by rw [h])
      have hgap : 2 ≤ |m - n| := two_le_abs_sub_of_even_sub (hpar m hm n hn) hmn
      refine delta_le_dist_of_two_le_abs_bucket_sub hδ ?_
      rw [hbm, hbn]
      exact hgap
  set Ge : Finset ℤ := G.filter fun n => Even n with hGe
  set Go : Finset ℤ := G.filter fun n => ¬ Even n with hGo
  have hsplit : Ge.card + Go.card = G.card :=
    Finset.card_filter_add_card_filter_not _
  have hGeG : Ge ⊆ G := Finset.filter_subset _ _
  have hGoG : Go ⊆ G := Finset.filter_subset _ _
  have hpare : ∀ m ∈ Ge, ∀ n ∈ Ge, Even (m - n) := by
    intro m hm n hn
    rw [hGe, Finset.mem_filter] at hm hn
    exact (Int.even_sub).mpr (by simp [hm.2, hn.2])
  have hparo : ∀ m ∈ Go, ∀ n ∈ Go, Even (m - n) := by
    intro m hm n hn
    rw [hGo, Finset.mem_filter] at hm hn
    exact (Int.even_sub).mpr (by simp [hm.2, hn.2])
  have hfinish : ∀ P : Finset ℝ, G.card ≤ 2 * P.card → S.card ≤ 2 * K * P.card := by
    intro P hGle
    calc S.card ≤ K * G.card := hcardS
      _ ≤ K * (2 * P.card) := Nat.mul_le_mul_left K hGle
      _ = 2 * K * P.card := by ring
  rcases le_total Ge.card Go.card with hcmp | hcmp
  · obtain ⟨P, hPS, hPcard, hPsep⟩ := hbuild Go hGoG hparo
    exact ⟨P, hPS, hfinish P (by omega), hPsep⟩
  · obtain ⟨P, hPS, hPcard, hPsep⟩ := hbuild Ge hGeG hpare
    exact ⟨P, hPS, hfinish P (by omega), hPsep⟩


/-! ### Disjoint cells: the mean-value input for a separated family

The Gallagher argument needs the cells attached to the chosen points to be pairwise disjoint and
contained in one interval.  For a `δ`-separated family both hold, so the sum of the cell integrals of
a nonnegative function is at most the integral over the enclosing interval.  This is what replaces
the telescoping used for a uniform grid. -/

open MeasureTheory

/-- Cells attached to a `δ`-separated family are pairwise disjoint. -/
theorem pairwise_disjoint_cells {δ : ℝ} (_hδ : 0 < δ) {P : Finset ℝ}
    (hPsep : ∀ x ∈ P, ∀ z ∈ P, x ≠ z → δ ≤ |x - z|) :
    (↑P : Set ℝ).PairwiseDisjoint (fun x : ℝ => Set.Ioc x (x + δ)) := by
  intro x hx z hz hxz
  have hsep := hPsep x hx z hz hxz
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro u hu hu'
  rcases le_total x z with hle | hle
  · have hxz' : x < z := lt_of_le_of_ne hle hxz
    have : δ ≤ z - x := by
      rw [abs_sub_comm, abs_of_pos (by linarith)] at hsep
      linarith
    exact absurd hu.2 (not_le.mpr (by linarith [hu'.1]))
  · have hzx : z < x := lt_of_le_of_ne hle (Ne.symm hxz)
    have : δ ≤ x - z := by
      rw [abs_of_pos (by linarith)] at hsep
      linarith
    exact absurd hu'.2 (not_le.mpr (by linarith [hu.1]))

/-- **Disjoint-cell mass bound.**  For a nonnegative integrable `g` and a `δ`-separated family `P`
inside `[A, B]`, the cell integrals sum to at most the integral over `(A, B+δ]`. -/
theorem sum_integral_cells_le {δ A B : ℝ} (hδ : 0 < δ) {g : ℝ → ℝ}
    (hg0 : ∀ u, 0 ≤ g u) (hgint : IntegrableOn g (Set.Ioc A (B + δ)))
    {P : Finset ℝ} (hPmem : ∀ x ∈ P, A ≤ x ∧ x ≤ B)
    (hPsep : ∀ x ∈ P, ∀ z ∈ P, x ≠ z → δ ≤ |x - z|) :
    ∑ x ∈ P, (∫ u in Set.Ioc x (x + δ), g u) ≤ ∫ u in Set.Ioc A (B + δ), g u := by
  classical
  have hcellsub : ∀ x ∈ P, Set.Ioc x (x + δ) ⊆ Set.Ioc A (B + δ) := by
    intro x hx u hu
    obtain ⟨hA, hB⟩ := hPmem x hx
    exact ⟨lt_of_le_of_lt hA hu.1, le_trans hu.2 (by linarith)⟩
  have hUsub : (⋃ x ∈ P, Set.Ioc x (x + δ)) ⊆ Set.Ioc A (B + δ) := by
    intro u hu
    rw [Set.mem_iUnion₂] at hu
    obtain ⟨x, hx, hux⟩ := hu
    exact hcellsub x hx hux
  have hmeas : ∀ x ∈ P, MeasurableSet (Set.Ioc x (x + δ)) := fun x _ => measurableSet_Ioc
  have hintOn : ∀ x ∈ P, IntegrableOn g (Set.Ioc x (x + δ)) :=
    fun x hx => hgint.mono_set (hcellsub x hx)
  have hsum : ∫ u in ⋃ x ∈ P, Set.Ioc x (x + δ), g u
      = ∑ x ∈ P, ∫ u in Set.Ioc x (x + δ), g u :=
    integral_biUnion_finset P hmeas (pairwise_disjoint_cells hδ hPsep) hintOn
  rw [← hsum]
  refine setIntegral_mono_set hgint ?_ (LE.le.eventuallyLE hUsub)
  exact Filter.Eventually.of_forall hg0



/-- **Gallagher's bound for a separated family.**  The corpus's `gallagher_grid` is stated for a
uniform grid, but its proof only uses that the cells are disjoint and lie in one interval.  For a
`δ`-separated family inside `[A, B]` the same conclusion holds over `[A, B+δ]`. -/
theorem gallagher_separated {f f' : ℝ → ℂ} {A B δ : ℝ} (hδ : 0 < δ) (hAB : A ≤ B)
    {P : Finset ℝ} (hPmem : ∀ x ∈ P, A ≤ x ∧ x ≤ B)
    (hPsep : ∀ x ∈ P, ∀ z ∈ P, x ≠ z → δ ≤ |x - z|)
    (hf : ∀ y ∈ Set.Icc A (B + δ), HasDerivAt f (f' y) y)
    (hg'int : IntervalIntegrable (fun y => 2 * inner ℝ (f y) (f' y)) volume A (B + δ))
    (hgint : IntervalIntegrable (fun y => ‖f y‖ ^ 2) volume A (B + δ))
    (hcrossint : IntervalIntegrable (fun y => 2 * (‖f y‖ * ‖f' y‖)) volume A (B + δ)) :
    ∑ x ∈ P, ‖f x‖ ^ 2
      ≤ (1 / δ) * (∫ u in A..B + δ, ‖f u‖ ^ 2)
        + ∫ u in A..B + δ, 2 * (‖f u‖ * ‖f' u‖) := by
  classical
  have hABδ : A ≤ B + δ := by linarith
  have hcellIcc : ∀ x ∈ P, Set.Icc x (x + δ) ⊆ Set.Icc A (B + δ) := by
    intro x hx
    obtain ⟨hA, hB⟩ := hPmem x hx
    exact Set.Icc_subset_Icc hA (by linarith)
  have hcelluIcc : ∀ x ∈ P, Set.uIcc x (x + δ) ⊆ Set.uIcc A (B + δ) := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le hABδ]
    exact hcellIcc x hx
  -- per-cell Sobolev bound at the left endpoint
  have hper : ∀ x ∈ P, ‖f x‖ ^ 2
      ≤ (1 / δ) * (∫ u in Set.Ioc x (x + δ), ‖f u‖ ^ 2)
        + ∫ u in Set.Ioc x (x + δ), 2 * (‖f u‖ * ‖f' u‖) := by
    intro x hx
    have hsub := hcellIcc x hx
    have hsubu := hcelluIcc x hx
    have h := sobolev_pointwise (f := f) (f' := f') (c := x) (δ := δ) hδ
      (fun y hy => hf y (hsub (by rwa [Set.uIcc_of_le (by linarith : x ≤ x + δ)] at hy)))
      (hg'int.mono_set hsubu) (hgint.mono_set hsubu) (hcrossint.mono_set hsubu)
      ⟨le_refl _, by linarith⟩
    rwa [intervalIntegral.integral_of_le (by linarith : x ≤ x + δ),
      intervalIntegral.integral_of_le (by linarith : x ≤ x + δ)] at h
  -- nonnegativity and integrability of the two densities
  have hsq0 : ∀ u : ℝ, 0 ≤ ‖f u‖ ^ 2 := fun u => sq_nonneg _
  have hcr0 : ∀ u : ℝ, 0 ≤ 2 * (‖f u‖ * ‖f' u‖) := fun u => by positivity
  have hsqOn : IntegrableOn (fun u => ‖f u‖ ^ 2) (Set.Ioc A (B + δ)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hABδ).mp hgint
  have hcrOn : IntegrableOn (fun u => 2 * (‖f u‖ * ‖f' u‖)) (Set.Ioc A (B + δ)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hABδ).mp hcrossint
  have hA1 := sum_integral_cells_le (g := fun u => ‖f u‖ ^ 2) hδ hsq0 hsqOn hPmem hPsep
  have hA2 := sum_integral_cells_le (g := fun u => 2 * (‖f u‖ * ‖f' u‖)) hδ hcr0 hcrOn hPmem hPsep
  have hδ0 : (0 : ℝ) ≤ 1 / δ := by positivity
  calc ∑ x ∈ P, ‖f x‖ ^ 2
      ≤ ∑ x ∈ P, ((1 / δ) * (∫ u in Set.Ioc x (x + δ), ‖f u‖ ^ 2)
          + ∫ u in Set.Ioc x (x + δ), 2 * (‖f u‖ * ‖f' u‖)) := Finset.sum_le_sum hper
    _ = (1 / δ) * (∑ x ∈ P, ∫ u in Set.Ioc x (x + δ), ‖f u‖ ^ 2)
          + ∑ x ∈ P, ∫ u in Set.Ioc x (x + δ), 2 * (‖f u‖ * ‖f' u‖) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ (1 / δ) * (∫ u in Set.Ioc A (B + δ), ‖f u‖ ^ 2)
          + ∫ u in Set.Ioc A (B + δ), 2 * (‖f u‖ * ‖f' u‖) := by
        have := mul_le_mul_of_nonneg_left hA1 hδ0
        linarith
    _ = (1 / δ) * (∫ u in A..B + δ, ‖f u‖ ^ 2)
          + ∫ u in A..B + δ, 2 * (‖f u‖ * ‖f' u‖) := by
        rw [intervalIntegral.integral_of_le hABδ, intervalIntegral.integral_of_le hABδ]



/-- **The large-values inequality for a separated family.**  If a `δ`-separated set `P ⊆ [A,B]` has
`‖f‖ ≥ V` at every point, its size is bounded by the second moments of `f` and `f'` over `[A, B+δ]`.
This is `large_values_count` with the uniform grid replaced by the weaker and usable hypothesis of
`δ`-separation. -/
theorem large_values_separated {f f' : ℝ → ℂ} {A B δ V η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hV0 : 0 ≤ V) (hAB : A ≤ B) {P : Finset ℝ}
    (hPmem : ∀ x ∈ P, A ≤ x ∧ x ≤ B)
    (hPsep : ∀ x ∈ P, ∀ z ∈ P, x ≠ z → δ ≤ |x - z|)
    (hf : ∀ y ∈ Set.Icc A (B + δ), HasDerivAt f (f' y) y)
    (hg'int : IntervalIntegrable (fun y => 2 * inner ℝ (f y) (f' y)) volume A (B + δ))
    (hgint : IntervalIntegrable (fun y => ‖f y‖ ^ 2) volume A (B + δ))
    (hsqf'int : IntervalIntegrable (fun y => ‖f' y‖ ^ 2) volume A (B + δ))
    (hcrossint : IntervalIntegrable (fun y => 2 * (‖f y‖ * ‖f' y‖)) volume A (B + δ))
    (hV : ∀ x ∈ P, V ≤ ‖f x‖) :
    (P.card : ℝ) * V ^ 2 ≤ (1 / δ + 1 / η) * (∫ u in A..B + δ, ‖f u‖ ^ 2)
      + η * (∫ u in A..B + δ, ‖f' u‖ ^ 2) := by
  have hABδ : A ≤ B + δ := by linarith
  have hlow : (P.card : ℝ) * V ^ 2 ≤ ∑ x ∈ P, ‖f x‖ ^ 2 := by
    calc (P.card : ℝ) * V ^ 2 = ∑ _x ∈ P, V ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ P, ‖f x‖ ^ 2 :=
          Finset.sum_le_sum fun x hx => pow_le_pow_left₀ hV0 (hV x hx) 2
  have hgal := gallagher_separated hδ hAB hPmem hPsep hf hg'int hgint hcrossint
  have hamgm : ∫ u in A..B + δ, 2 * (‖f u‖ * ‖f' u‖)
      ≤ ∫ u in A..B + δ, (‖f u‖ ^ 2 / η + η * ‖f' u‖ ^ 2) := by
    refine intervalIntegral.integral_mono_on hABδ hcrossint
      ((hgint.div_const η).add (hsqf'int.const_mul η)) ?_
    intro u _
    have h := two_mul_le_div_add_mul (a := ‖f u‖) (b := ‖f' u‖) hη
    linarith
  have hsplit : ∫ u in A..B + δ, (‖f u‖ ^ 2 / η + η * ‖f' u‖ ^ 2)
      = (1 / η) * (∫ u in A..B + δ, ‖f u‖ ^ 2) + η * (∫ u in A..B + δ, ‖f' u‖ ^ 2) := by
    rw [intervalIntegral.integral_add (hgint.div_const η) (hsqf'int.const_mul η),
      intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
    ring
  rw [hsplit] at hamgm
  linarith



/-- **Counting detected points from a second moment.**  Any finite set on which `‖f‖ ≥ V`, lying in
`[A,B]` with at most `K` points per bucket of scale `δ`, has size bounded by the second moments of
`f` and `f'` over `[A, B+δ]`, with the local-density factor `2K`:

```text
|Z| · V² ≤ 2K · ( (δ⁻¹ + η⁻¹)∫‖f‖² + η∫‖f'‖² ) .
```

This is the counting step of a density argument, stated with the local bound `K` and the moment
bounds as hypotheses.  Applied to ordinates of zeta zeros with `re ρ ≥ σ` it is the shape Carlson's
theorem consumes, `K` being the local Riemann–von Mangoldt count. -/
theorem card_le_of_large_values {f f' : ℝ → ℂ} {A B δ V η : ℝ} {K : ℕ}
    (hδ : 0 < δ) (hη : 0 < η) (hV0 : 0 ≤ V) (hAB : A ≤ B) {Z : Finset ℝ}
    (hZmem : ∀ x ∈ Z, A ≤ x ∧ x ≤ B)
    (hloc : ∀ n : ℤ, (Z.filter fun x => bucket δ x = n).card ≤ K)
    (hdet : ∀ x ∈ Z, V ≤ ‖f x‖)
    (hf : ∀ y ∈ Set.Icc A (B + δ), HasDerivAt f (f' y) y)
    (hg'int : IntervalIntegrable (fun y => 2 * inner ℝ (f y) (f' y)) volume A (B + δ))
    (hgint : IntervalIntegrable (fun y => ‖f y‖ ^ 2) volume A (B + δ))
    (hsqf'int : IntervalIntegrable (fun y => ‖f' y‖ ^ 2) volume A (B + δ))
    (hcrossint : IntervalIntegrable (fun y => 2 * (‖f y‖ * ‖f' y‖)) volume A (B + δ)) :
    (Z.card : ℝ) * V ^ 2 ≤ 2 * K *
      ((1 / δ + 1 / η) * (∫ u in A..B + δ, ‖f u‖ ^ 2)
        + η * (∫ u in A..B + δ, ‖f' u‖ ^ 2)) := by
  obtain ⟨P, hPZ, hPcard, hPsep⟩ := exists_wellSpaced_subset hδ Z hloc
  have hPmem : ∀ x ∈ P, A ≤ x ∧ x ≤ B := fun x hx => hZmem x (hPZ hx)
  have hPdet : ∀ x ∈ P, V ≤ ‖f x‖ := fun x hx => hdet x (hPZ hx)
  have hcount := large_values_separated hδ hη hV0 hAB hPmem hPsep hf hg'int hgint hsqf'int
    hcrossint hPdet
  have hcast : (Z.card : ℝ) ≤ 2 * K * P.card := by exact_mod_cast hPcard
  have hsq : (0 : ℝ) ≤ V ^ 2 := sq_nonneg V
  have hKnn : (0 : ℝ) ≤ 2 * K := by positivity
  calc (Z.card : ℝ) * V ^ 2 ≤ (2 * K * P.card) * V ^ 2 :=
        mul_le_mul_of_nonneg_right hcast hsq
    _ = 2 * K * ((P.card : ℝ) * V ^ 2) := by ring
    _ ≤ 2 * K * ((1 / δ + 1 / η) * (∫ u in A..B + δ, ‖f u‖ ^ 2)
          + η * (∫ u in A..B + δ, ‖f' u‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hcount hKnn


end RHTower
