import GaloisForLFunctions.HTGeometry.SchurCornerRatio
import GaloisForLFunctions.HTGeometry.CauchyBinet

/-!
# Perturbations of geometric products keep low-order Toeplitz minors positive

Let `a` be the coefficient sequence of `∏ 1/(1 − x_s u)` with `x₁ ≥ x₂ ≥ … ≥ 0`, let `k ≥ m` with
`x_k > 0`, and put `ρ = k/x_k`.  For any real sequence `q` with `q₀ = 1` and
`Σ_t |q_t| ρ^t ≤ Q`, every Toeplitz minor of order `m` of the Cauchy product `a ∗ q` satisfies

`det ((a ∗ q)_{j_c − i_r}) ≥ (2 − Q^m) · det (a_{j_c − i_r})`

(`toeplitzMinor_cauchyConv_ge_of_perturbation`).  In particular the minors of `a ∗ q` stay
nonnegative as long as `Q^m ≤ 2`: a perturbation that is small at the scale `x_k/k` cannot destroy
total positivity of order `k`.

The minor of `a ∗ q` expands over all column choices `f`:
`det (A·B) = Σ_f (∏_c q_{j_c − f_c}) det (a_{f_c − i_r})`.  The term `f = j` is the minor of `a`.
For the others, sorting the columns gives a minor of `a` at strictly increasing columns `g ≤ j`
(a pigeonhole argument).  Lowering the columns of `j` down to `g`, one at a time and keeping them
strictly increasing, costs at most `ρ` per unit by the corner ratio (`cornerRatio_single`).  The
weights then sum to `∏_c Σ_{t ≤ j_c} |q_t| ρ^t − 1 ≤ Q^m − 1`.
-/

open Finset Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Column form of the expansion of a rectangular product determinant. -/
theorem det_mul_eq_sum_fun_col {m N : ℕ} (A : Matrix (Fin m) (Fin N) ℝ)
    (B : Matrix (Fin N) (Fin m) ℝ) :
    (A * B).det = ∑ f : Fin m → Fin N, (∏ c, B (f c) c) * (A.submatrix id f).det := by
  rw [← Matrix.det_transpose, Matrix.transpose_mul, GaloisForLFunctions.det_mul_eq_sum_fun]
  refine Finset.sum_congr rfl fun f _ => ?_
  congr 1
  exact Matrix.det_transpose (A.submatrix id f)

/-- Entries of a decreasing list of nonnegative reals decrease along the index. -/
theorem getD_antitone {xs : List ℝ} (hsort : xs.Pairwise (· ≥ ·)) (hnn : ∀ x ∈ xs, 0 ≤ x)
    {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) : xs.getD n₂ 0 ≤ xs.getD n₁ 0 := by
  rcases Nat.lt_or_ge n₂ xs.length with h₂ | h₂
  · have h₁ : n₁ < xs.length := lt_of_le_of_lt h h₂
    rw [List.getD_eq_getElem _ _ h₂, List.getD_eq_getElem _ _ h₁]
    rcases Nat.eq_or_lt_of_le h with e | hlt
    · subst e; exact le_rfl
    · exact List.pairwise_iff_getElem.mp hsort n₁ n₂ h₁ h₂ hlt
  · rw [List.getD_eq_default _ _ h₂]
    rcases Nat.lt_or_ge n₁ xs.length with h₁ | h₁
    · rw [List.getD_eq_getElem _ _ h₁]; exact hnn _ (List.getElem_mem h₁)
    · rw [List.getD_eq_default _ _ h₁]

section Bounds

variable {xs : List ℝ} (hsort : xs.Pairwise (· ≥ ·)) (hnn : ∀ x ∈ xs, 0 ≤ x)
  {k m : ℕ} (hmk : m ≤ k) (hxk : 0 < xs.getD (k - 1) 0)

include hsort hnn hmk hxk

/-- One column decrement costs at most `k/x_k` for minors of order `m ≤ k`. -/
theorem toeplitzMinor_colDecr_le {i j : Fin m → ℕ} (hi : StrictMono i) (hj : StrictMono j)
    {c : Fin m} (hjc : 0 < j c) :
    toeplitzMinor (geomProdSeq xs) m i (colDecr j c) ≤
      (k / xs.getD (k - 1) 0) * toeplitzMinor (geomProdSeq xs) m i j := by
  set r := m - c.val with hr
  have hcr : m ≤ c.val + r := by omega
  have h := cornerRatio_single hsort hnn hi hj hcr hjc
  have hrk : r ≤ k := by omega
  have hxr : xs.getD (k - 1) 0 ≤ xs.getD (r - 1) 0 := getD_antitone hsort hnn (by omega)
  have hM0 := toeplitzMinor_colDecr_nonneg (pfSeq_geomProdSeq hnn m) hi hj c
  have hM : 0 ≤ toeplitzMinor (geomProdSeq xs) m i j := pfSeq_geomProdSeq hnn m m le_rfl i j hi hj
  rw [div_mul_eq_mul_div, le_div_iff₀ hxk]
  calc toeplitzMinor (geomProdSeq xs) m i (colDecr j c) * xs.getD (k - 1) 0
      ≤ xs.getD (r - 1) 0 * toeplitzMinor (geomProdSeq xs) m i (colDecr j c) := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right hxr hM0
    _ ≤ r * toeplitzMinor (geomProdSeq xs) m i j := h
    _ ≤ k * toeplitzMinor (geomProdSeq xs) m i j :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hrk) hM

/-- **Iterated corner ratio.**  For strictly increasing `l ≤ j`,
`M(l) ≤ (k/x_k)^{|j| − |l|} M(j)`. -/
theorem toeplitzMinor_le_pow_of_le {i : Fin m → ℕ} (hi : StrictMono i) :
    ∀ (d : ℕ) (j l : Fin m → ℕ), StrictMono j → StrictMono l → (∀ c, l c ≤ j c) →
      ∑ c, (j c - l c) = d →
        toeplitzMinor (geomProdSeq xs) m i l ≤
          (k / xs.getD (k - 1) 0) ^ d * toeplitzMinor (geomProdSeq xs) m i j := by
  classical
  have hρ : 0 ≤ (k : ℝ) / xs.getD (k - 1) 0 := div_nonneg (Nat.cast_nonneg _) hxk.le
  intro d
  induction d with
  | zero =>
    intro j l _ _ hle hsum
    have hjl : l = j := funext fun c => by
      have := (Finset.sum_eq_zero_iff.mp hsum) c (Finset.mem_univ c)
      have := hle c
      omega
    rw [hjl, pow_zero, one_mul]
  | succ d ih =>
    intro j l hj hl hle hsum
    -- the first column where `l` is below `j`
    have hex : ((univ : Finset (Fin m)).filter fun c => l c < j c).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hne
      have : ∀ c, j c - l c = 0 := fun c => by
        have := hne (Finset.mem_univ c); have := hle c; omega
      simp [this] at hsum
    set c := ((univ : Finset (Fin m)).filter fun c => l c < j c).min' hex with hc
    have hcmem := Finset.min'_mem _ hex
    rw [← hc, Finset.mem_filter] at hcmem
    have hlc : l c < j c := hcmem.2
    have hbefore : ∀ c', c' < c → l c' = j c' := fun c' hc' => by
      by_contra hne
      have hlt : l c' < j c' := lt_of_le_of_ne (hle c') hne
      have := Finset.min'_le _ c'
        (Finset.mem_filter.mpr ⟨Finset.mem_univ c', hlt⟩ :
          c' ∈ (univ : Finset (Fin m)).filter fun c => l c < j c)
      rw [← hc] at this
      exact absurd hc' (not_lt.mpr this)
    have hjc : 0 < j c := by omega
    -- lowering column `c` keeps `j` strictly increasing
    have hj' : StrictMono (colDecr j c) := by
      intro c₁ c₂ h12
      by_cases h1 : c₁ = c
      · subst h1
        simp only [colDecr, Function.update_self, Function.update_of_ne (ne_of_gt h12)]
        have := hj h12; omega
      · by_cases h2 : c₂ = c
        · subst h2
          simp only [colDecr, Function.update_self, Function.update_of_ne h1]
          have e := hbefore c₁ h12
          have := hl h12
          omega
        · simp only [colDecr, Function.update_of_ne h1, Function.update_of_ne h2]
          exact hj h12
    have hle' : ∀ c', l c' ≤ colDecr j c c' := fun c' => by
      by_cases h : c' = c
      · subst h; simp only [colDecr, Function.update_self]; omega
      · simp only [colDecr, Function.update_of_ne h]; exact hle c'
    have hsum' : ∑ c', (colDecr j c c' - l c') = d := by
      have h1 := sum_sub_eq_sum_colDecr_sub_add_one hjc hle'
      omega
    have h1 := ih (colDecr j c) l hj' hl hle' hsum'
    have h2 := toeplitzMinor_colDecr_le hsort hnn hmk hxk hi hj hjc
    calc toeplitzMinor (geomProdSeq xs) m i l
        ≤ (k / xs.getD (k - 1) 0) ^ d * toeplitzMinor (geomProdSeq xs) m i (colDecr j c) := h1
      _ ≤ (k / xs.getD (k - 1) 0) ^ d *
            ((k / xs.getD (k - 1) 0) * toeplitzMinor (geomProdSeq xs) m i j) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hρ _)
      _ = (k / xs.getD (k - 1) 0) ^ (d + 1) * toeplitzMinor (geomProdSeq xs) m i j := by ring

end Bounds

/-- **Pigeonhole for sorted columns.**  If an injective `f` lies below a strictly increasing `j`,
so does its increasing rearrangement. -/
theorem sort_le_of_le {m N : ℕ} {f : Fin m → Fin N} (hf : Function.Injective f)
    {j : Fin m → ℕ} (hj : StrictMono j) (hle : ∀ c, (f c : ℕ) ≤ j c) (c : Fin m) :
    ((f ∘ Tuple.sort f) c : ℕ) ≤ j c := by
  classical
  set σ := Tuple.sort f with hσ
  set g := f ∘ σ with hg
  have hgmono : StrictMono g := (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
  by_contra hgt
  push Not at hgt
  -- `σ` maps `[c, m)` injectively into `(c, m)`
  have hmaps : Set.MapsTo σ (Finset.Ici c : Set (Fin m)) (Finset.Ioi c : Set (Fin m)) := by
    intro d hd
    rw [Finset.coe_Ici, Set.mem_Ici] at hd
    rw [Finset.coe_Ioi, Set.mem_Ioi]
    have hgd : g c ≤ g d := hgmono.monotone hd
    have h1 : j c < (f (σ d) : ℕ) := by
      have : (g d : ℕ) = f (σ d) := rfl
      have := Fin.le_def.mp hgd
      omega
    have h2 := hle (σ d)
    by_contra hcd
    push Not at hcd
    have := hj.monotone hcd
    omega
  have hcard := Finset.card_le_card_of_injOn σ hmaps σ.injective.injOn
  rw [Fin.card_Ici, Fin.card_Ioi] at hcard
  have := c.isLt
  omega

/-- **Sorting bound.**  A column choice `f ≤ j` gives a minor of absolute value at most
`(k/x_k)^{Σ (j_c − f_c)} M(j)`. -/
theorem abs_det_submatrix_le {xs : List ℝ} (hsort : xs.Pairwise (· ≥ ·)) (hnn : ∀ x ∈ xs, 0 ≤ x)
    {k m N : ℕ} (hmk : m ≤ k) (hxk : 0 < xs.getD (k - 1) 0) {i j : Fin m → ℕ}
    (hi : StrictMono i) (hj : StrictMono j) (f : Fin m → Fin N) (hle : ∀ c, (f c : ℕ) ≤ j c) :
    |((Matrix.of fun r (l : Fin N) => zext (geomProdSeq xs) ((l : ℤ) - i r)).submatrix id f).det| ≤
      (k / xs.getD (k - 1) 0) ^ (∑ c, (j c - (f c : ℕ))) *
        toeplitzMinor (geomProdSeq xs) m i j := by
  classical
  set A : Matrix (Fin m) (Fin N) ℝ := Matrix.of fun r (l : Fin N) =>
    zext (geomProdSeq xs) ((l : ℤ) - i r) with hA
  have hρ : 0 ≤ (k : ℝ) / xs.getD (k - 1) 0 := div_nonneg (Nat.cast_nonneg _) hxk.le
  have hM : 0 ≤ toeplitzMinor (geomProdSeq xs) m i j := pfSeq_geomProdSeq hnn m m le_rfl i j hi hj
  by_cases hf : Function.Injective f
  · set σ := Tuple.sort f with hσ
    set g := f ∘ σ with hg
    have hgmono : StrictMono g :=
      (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
    set gN : Fin m → ℕ := fun c => (g c : ℕ) with hgN
    have hgN : StrictMono gN := Fin.val_strictMono.comp hgmono
    have hsub : A.submatrix id f = (A.submatrix id g).submatrix id (σ⁻¹ : Equiv.Perm (Fin m)) := by
      ext r c; simp [hg]
    have hdetg : (A.submatrix id g).det = toeplitzMinor (geomProdSeq xs) m i gN := rfl
    have hgle : ∀ c, gN c ≤ j c := sort_le_of_le hf hj hle
    have hsumg : ∑ c, (j c - gN c) = ∑ c, (j c - (f c : ℕ)) := by
      rw [Finset.sum_tsub_distrib _ fun c _ => hgle c,
        Finset.sum_tsub_distrib _ fun c _ => hle c]
      congr 1
      exact Equiv.sum_comp σ (fun c => (f c : ℕ))
    rw [hsub, Matrix.det_permute', hdetg, abs_mul]
    have hsign : |((Equiv.Perm.sign (σ⁻¹ : Equiv.Perm (Fin m)) : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (σ⁻¹ : Equiv.Perm (Fin m))) with h | h <;>
        simp [h]
    rw [hsign, one_mul, abs_of_nonneg (pfSeq_geomProdSeq hnn m m le_rfl i gN hi hgN), ← hsumg]
    exact toeplitzMinor_le_pow_of_le hsort hnn hmk hxk hi _ j gN hj hgN hgle rfl
  · obtain ⟨c₁, c₂, h12, hne⟩ : ∃ c₁ c₂, f c₁ = f c₂ ∧ c₁ ≠ c₂ := by
      simp only [Function.Injective, not_forall] at hf
      obtain ⟨c₁, c₂, h1, h2⟩ := hf
      exact ⟨c₁, c₂, h1, h2⟩
    rw [det_zero_of_column_eq hne fun r => by simp [h12], abs_zero]
    exact mul_nonneg (pow_nonneg hρ _) hM

/-- **Perturbation of a geometric product.**  With `ρ = k/x_k`, `q₀ = 1` and
`Σ_{t < T} |q_t| ρ^t ≤ Q` for all `T`, every minor of order `m ≤ k` of `a ∗ q` is at least
`(2 − Q^m)` times the corresponding minor of `a`. -/
theorem toeplitzMinor_cauchyConv_ge_of_perturbation {xs : List ℝ} (hsort : xs.Pairwise (· ≥ ·))
    (hnn : ∀ x ∈ xs, 0 ≤ x) {k m : ℕ} (hmk : m ≤ k) (hxk : 0 < xs.getD (k - 1) 0)
    {q : ℕ → ℝ} (hq0 : q 0 = 1) {Q : ℝ}
    (hQ : ∀ T, ∑ t ∈ range T, |q t| * (k / xs.getD (k - 1) 0) ^ t ≤ Q)
    {i j : Fin m → ℕ} (hi : StrictMono i) (hj : StrictMono j) :
    (2 - Q ^ m) * toeplitzMinor (geomProdSeq xs) m i j ≤
      toeplitzMinor (cauchyConv (geomProdSeq xs) q) m i j := by
  classical
  set ρ : ℝ := k / xs.getD (k - 1) 0 with hρdef
  have hρ : 0 ≤ ρ := div_nonneg (Nat.cast_nonneg _) hxk.le
  set N := (∑ c, j c) + 1 with hNdef
  have hN : ∀ c, j c < N := fun c =>
    Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c))
  set a := geomProdSeq xs with ha
  set A : Matrix (Fin m) (Fin N) ℝ := Matrix.of fun r (l : Fin N) => zext a ((l : ℤ) - i r) with hA
  set B : Matrix (Fin N) (Fin m) ℝ := Matrix.of fun (l : Fin N) c => zext q ((j c : ℤ) - l) with hB
  set M := toeplitzMinor a m i j with hMdef
  have hM : 0 ≤ M := pfSeq_geomProdSeq hnn m m le_rfl i j hi hj
  rw [toeplitzMinor_cauchyConv a q m i j N hN, ← hA, ← hB, det_mul_eq_sum_fun_col]
  set jN : Fin m → Fin N := fun c => ⟨j c, hN c⟩ with hjN
  -- weights
  set w : (Fin m → Fin N) → ℝ := fun f =>
    ∏ c, (if (f c : ℕ) ≤ j c then |q (j c - f c)| * ρ ^ (j c - (f c : ℕ)) else 0) with hw
  have hterm : ∀ f, |(∏ c, B (f c) c) * (A.submatrix id f).det| ≤ w f * M := by
    intro f
    by_cases hle : ∀ c, (f c : ℕ) ≤ j c
    · have hB' : ∀ c, B (f c) c = q (j c - f c) := fun c => by
        simp only [hB, Matrix.of_apply]
        rw [show ((j c : ℤ) - (f c : ℕ)) = ((j c - (f c : ℕ) : ℕ) : ℤ) by push_cast [hle c]; ring,
          zext_natCast]
      rw [abs_mul, Finset.abs_prod]
      simp only [hB']
      have hw' : w f = (∏ c, |q (j c - f c)|) * ρ ^ (∑ c, (j c - (f c : ℕ))) := by
        rw [hw]
        simp only [if_pos (hle _), Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      rw [hw', mul_assoc]
      exact mul_le_mul_of_nonneg_left (abs_det_submatrix_le hsort hnn hmk hxk hi hj f hle)
        (Finset.prod_nonneg fun c _ => abs_nonneg _)
    · push Not at hle
      obtain ⟨c, hc⟩ := hle
      have hB0 : B (f c) c = 0 := by
        simp only [hB, Matrix.of_apply]
        exact zext_of_neg _ (by omega)
      rw [Finset.prod_eq_zero (f := fun c' => B (f c') c') (Finset.mem_univ c) hB0, zero_mul,
        abs_zero]
      have hw0 : w f = 0 := by
        rw [hw]
        exact Finset.prod_eq_zero (Finset.mem_univ c) (by rw [if_neg (by omega)])
      rw [hw0, zero_mul]
  -- the total weight
  have hwsum : ∑ f, w f ≤ Q ^ m := by
    have hprod : ∑ f, w f = ∏ c, ∑ v : Fin N,
        (if (v : ℕ) ≤ j c then |q (j c - v)| * ρ ^ (j c - (v : ℕ)) else 0) := by
      rw [Finset.prod_univ_sum]
      rw [Fintype.piFinset_univ]
    rw [hprod]
    have hQm : Q ^ m = ∏ _c : Fin m, Q := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hQm]
    refine Finset.prod_le_prod (fun c _ => Finset.sum_nonneg fun v _ => by
      split_ifs <;> positivity) fun c _ => ?_
    have hre : ∑ v : Fin N, (if (v : ℕ) ≤ j c then |q (j c - v)| * ρ ^ (j c - (v : ℕ)) else 0) =
        ∑ t ∈ range (j c + 1), |q t| * ρ ^ t := by
      rw [Fin.sum_univ_eq_sum_range (fun v => if v ≤ j c then |q (j c - v)| * ρ ^ (j c - v) else 0)]
      rw [← Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_of_lt (hN c)))
        (f := fun v => if v ≤ j c then |q (j c - v)| * ρ ^ (j c - v) else 0) (fun v _ hv => by
          rw [Finset.mem_range] at hv
          rw [if_neg (by omega)])]
      rw [Finset.sum_congr rfl fun v hv => by
        rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hv))]]
      exact Finset.sum_range_reflect (fun t => |q t| * ρ ^ t) (j c + 1)
    rw [hre]
    exact hQ _
  have hwj : w jN = 1 := by
    rw [hw]
    refine Finset.prod_eq_one fun c _ => ?_
    simp [hjN, hq0]
  have hdetj : (∏ c, B (jN c) c) * (A.submatrix id jN).det = M := by
    have : ∏ c, B (jN c) c = 1 := Finset.prod_eq_one fun c _ => by
      simp [hB, hjN, zext, hq0]
    rw [this, one_mul]
    rfl
  -- assemble
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ jN), hdetj]
  have hrest : -(∑ f ∈ univ.erase jN, w f) * M ≤
      ∑ f ∈ univ.erase jN, (∏ c, B (f c) c) * (A.submatrix id f).det := by
    rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun f _ => neg_le_of_abs_le (hterm f)
  have hsum_erase : ∑ f ∈ univ.erase jN, w f ≤ Q ^ m - 1 := by
    have := Finset.add_sum_erase (univ : Finset (Fin m → Fin N)) w (Finset.mem_univ jN)
    rw [hwj] at this
    linarith
  nlinarith

end

end GaloisForLFunctions.HTGeometry
