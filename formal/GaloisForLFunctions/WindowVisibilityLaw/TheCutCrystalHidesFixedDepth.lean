import GaloisForLFunctions.WindowVisibilityLaw.ShallowClusterExclusionAndTaperedCrystalBarrier
import GaloisForLFunctions.WindowVisibilityLaw.TheSineLocalizerOfATest

/-!
# The cut crystal hides a fixed depth

A doubled lattice of density `L` cannot satisfy a uniform Riemann–von Mangoldt bound near height
zero when `L ≍ log T`. Remove its points below height `t₀ = e^L`: the count is then uniform, but a
test may hide mass where points were removed, and the crystal floor `2L‖f‖²` is lost.

The localizer restores it. Apply the floor to `g = sinePower τ N f` with `τT = π/2`:

* on-line terms only decrease, because `|sin(τx)| ≤ 1` on the real line;
* the removed points cost `(r/R)^{2N}`, by the zero of order `N` of the localizer at height zero;
* near the packet the localizer is `1 + O(Nτ²Π²)`, so the off-line terms are unchanged.

This gives `Re W(f,f) ≥ (5/4) L ‖g‖² ≥ 0` for every test, and a zero of any fixed depth at height `T`
hides from aperture `(log T)/36` in a configuration with `N(t,t+1] ≤ log(|t|+3)`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.WindowVisibilityLaw

open Zeta23 _root_.RHTower
open GaloisForLFunctions.SquareRootThreshold

/-- The doubled lattice of density `L` with the on-line ordinates in `R` removed and the pairs
`½ ± d_k + 2πik/L`, `k ∈ S`, in place of the double on-line points of `S`. -/
def cutClusterConfig {L : ℝ} (hL : 0 < L) (R S : Finset ℤ) (d : ℤ → ℝ) (hd0 : ∀ k ∈ S, 0 < d k)
    (hd1 : ∀ k ∈ S, d k ≤ 1 / 2) : ZeroConfig where
  carrier := ((Set.range fun k : {k : ℤ // k ∉ S ∪ R} => verticalLatticePoint L 0 k) ∪
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

/-- Grid Parseval for the doubled lattice below the Nyquist aperture. -/
theorem hasSum_two_norm_sq_lattice {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) :
    HasSum (fun k : ℤ => 2 * ‖paperFT f (((k : ℝ) * (2 * π / L) : ℝ) : ℂ)‖ ^ 2)
      (2 * L * ∫ t, ‖f t‖ ^ 2) := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hK := EF.weilTest_contDiff hf hf.continuous hfc
  have hKs := weilTest_abs_le hfs hfs
  have h0 := tsum_weilTest_lattice_eq hL hf hf.continuous hfs hfs
    (fun m : ℤ => (Real.exp (0 * (m * L)) : ℂ)) (by simp)
  have h2 := (hasSum_paperFT_lattice_sub_I_mul hL hK hKs 0).mul_left 2
  rw [h0, integral_mul_conj_self_eq] at h2
  have hfun : (fun i : ℤ => 2 * paperFT (EF.weilTest f f)
      ((((i : ℝ) * (2 * π / L) : ℝ) : ℂ) - I * ((0 : ℝ) : ℂ))) =
      fun k : ℤ => ((2 * ‖paperFT f (((k : ℝ) * (2 * π / L) : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    funext k
    have e : (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) - I * ((0 : ℝ) : ℂ) =
        (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) := by simp
    rw [e, paperFT_weilTest_self_ofReal hf.continuous hfc]
    push_cast
    ring
  have hval : (2 : ℂ) * ((L : ℂ) * ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ)) =
      ((2 * L * ∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hfun, hval] at h2
  exact Complex.hasSum_ofReal.mp h2

/-- The Weil form of the cut cluster below the Nyquist aperture. -/
theorem W_cutClusterConfig {L : ℝ} (hL : 0 < L) (R S : Finset ℤ) (hRS : Disjoint S R) (d : ℤ → ℝ)
    (hd0 : ∀ k ∈ S, 0 < d k) (hd1 : ∀ k ∈ S, d k ≤ 1 / 2)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) :
    (cutClusterConfig hL R S d hd0 hd1).W f f = 2 * L * (∫ t, f t * conj (f t)) +
      ∑ k ∈ S, (paperFT (EF.weilTest f f) ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) - I * d k) +
        paperFT (EF.weilTest f f) ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) + I * d k) -
        2 * paperFT (EF.weilTest f f) (((k : ℝ) * (2 * π / L) : ℝ) : ℂ)) -
      ∑ k ∈ R, 2 * paperFT (EF.weilTest f f) (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) := by
  set Z := cutClusterConfig hL R S d hd0 hd1 with hZ
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
  have hA : HasSum (fun ρ : Set.range (fun k : {k : ℤ // k ∉ S ∪ R} => verticalLatticePoint L 0 k) =>
      Z.Wsummand f f ρ) (2 * L * (∫ t, f t * conj (f t)) -
        ∑ k ∈ S ∪ R, 2 * paperFT K (((k : ℝ) * (2 * π / L) : ℝ) : ℂ)) := by
    have hinj : Function.Injective (fun k : {k : ℤ // k ∉ S ∪ R} => verticalLatticePoint L 0 k) :=
      fun k k' h => Subtype.ext (verticalLatticePoint_injective hL 0 h)
    rw [hinj.hasSum_range_iff]
    have := (Finset.hasSum_compl_iff
      (f := fun k : ℤ => 2 * paperFT K (((k : ℝ) * (2 * π / L) : ℝ) : ℂ)) (S ∪ R)).mpr
      (by rwa [sub_add_cancel])
    have hfun : (Z.Wsummand f f ∘ fun k : {k : ℤ // k ∉ S ∪ R} => verticalLatticePoint L 0 k) =
        fun x : {k : ℤ // k ∉ S ∪ R} => 2 * paperFT K ((((x : ℤ) : ℝ) * (2 * π / L) : ℝ) : ℂ) :=
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
  have hd₁ : Disjoint (Set.range fun k : {k : ℤ // k ∉ S ∪ R} => verticalLatticePoint L 0 k)
      (Set.range fun k : S => verticalLatticePoint L (d k) k) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ ⟨k', hk'⟩
    have := congrArg Complex.re hk'
    simp only [verticalLatticePoint] at this
    linarith [hd0 k' k'.2]
  have hd₂ : Disjoint ((Set.range fun k : {k : ℤ // k ∉ S ∪ R} => verticalLatticePoint L 0 k) ∪
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
    Finset.sum_union hRS, ← Finset.sum_coe_sort S (fun k => 2 * paperFT K _)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- **The localized crystal floor.** If the biquadratic packet has a small tapering error at the
enlarged aperture `A = a + Nτ`, the removed ordinates are paid by the zero of the localizer, and the
localizer is close to one on the packet, then the cut crystal is window-positive at `a`. -/
theorem windowPositiveAt_cutCrystal {L δ a τ T r Rr ρ : ℝ} (hL : 0 < L) (k₀ : ℤ) {M N : ℕ}
    (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (ha : 0 ≤ a) (hτ : 0 ≤ τ)
    (hτT : τ * T = π / 2) (hA4 : 4 * (a + N * τ) ≤ L) (R : Finset ℤ)
    (hRS : Disjoint (taperedSupport k₀ M) R)
    (hfloor : 38 * (a + N * τ) * L * δ ^ 2 * Real.cosh (2 * δ * (a + N * τ)) / (M : ℝ) ≤ 1 / 8)
    (hr : 0 < r) (hrR : r ≤ Rr) (hlow : ∀ k ∈ R, |(k : ℝ) * (2 * π / L)| ≤ r)
    (hlowsum : (R.card : ℝ) * (2 * ((r / Rr) ^ (2 * N) *
      (4 * (a + N * τ) * Real.exp (2 * (a + N * τ) * Rr)))) ≤ L / 4)
    (hρ1 : ρ ≤ 1) (hρ2 : ((2 * N : ℕ) : ℝ) * ρ ^ 2 ≤ 1 / 4)
    (hnear : ∀ k ∈ taperedSupport k₀ M, ∀ y : ℝ, |y| ≤ δ →
      ‖(τ : ℂ) * ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) + I * y - T)‖ ≤ ρ)
    (hnearsum : ((taperedSupport k₀ M).card : ℝ) * (2 * (2 * (2 * (((2 * N : ℕ) : ℝ) * ρ ^ 2)) *
      (4 * (a + N * τ) * Real.exp (2 * (a + N * τ) * δ)))) ≤ L / 4) :
    WindowPositiveAt (cutClusterConfig hL R (taperedSupport k₀ M) (biquadraticProfile k₀ M δ)
      (fun _ hk => biquadraticProfile_pos k₀ hδ0 hk)
      (fun _ hk => (biquadraticProfile_le k₀ M hδ0.le hk).trans hδ1)) a := by
  intro f hf hfs
  set A := a + N * τ with hA
  have hNτ : 0 ≤ (N : ℝ) * τ := by positivity
  have haA : a ≤ A := by rw [hA]; linarith only [hNτ]
  have hA0 : 0 ≤ A := ha.trans haA
  set S := taperedSupport k₀ M with hS
  set d := biquadraticProfile k₀ M δ with hd
  have hd0 : ∀ k ∈ S, 0 < d k := fun _ hk => biquadraticProfile_pos k₀ hδ0 hk
  have hd1 : ∀ k ∈ S, d k ≤ δ := fun _ hk => biquadraticProfile_le k₀ M hδ0.le hk
  have hd2 : ∀ k ∈ S, d k ≤ 1 / 2 := fun k hk => (hd1 k hk).trans hδ1
  have hLA : A ≤ L / 4 := by linarith only [hA4]
  have hsubL : ∀ {B : ℝ}, B ≤ L / 4 → 0 ≤ B → Icc (-B) B ⊆ Icc (-(L / 2)) (L / 2) := fun hB hB0 =>
    Icc_subset_Icc (by linarith only [hB, hB0, hL]) (by linarith only [hB, hB0, hL])
  have hfsL : tsupport f ⊆ Icc (-(L / 2)) (L / 2) :=
    hfs.trans (hsubL (haA.trans hLA) ha)
  set g := sinePower τ N f with hg
  have hgc : ContDiff ℝ 2 g := contDiff_sinePower τ N hf
  have hgs : tsupport g ⊆ Icc (-A) A := tsupport_sinePower_subset hτ N hfs
  have hgsL : tsupport g ⊆ Icc (-(L / 2)) (L / 2) := hgs.trans (hsubL hLA hA0)
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hgcs := hasCompactSupport_of_tsupport_subset_Icc hgs
  set Nf := ∫ t, ‖f t‖ ^ 2 with hNf
  set Ng := ∫ t, ‖g t‖ ^ 2 with hNg
  have hNg0 : 0 ≤ Ng := integral_nonneg fun _ => sq_nonneg _
  let lf : ℤ → ℝ := fun k => ‖paperFT f (((k : ℝ) * (2 * π / L) : ℝ) : ℂ)‖ ^ 2
  let lg : ℤ → ℝ := fun k => ‖paperFT g (((k : ℝ) * (2 * π / L) : ℝ) : ℂ)‖ ^ 2
  have hPf : ∀ k : ℤ, paperFT (EF.weilTest f f) (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) =
      ((lf k : ℝ) : ℂ) := fun k => paperFT_weilTest_self_ofReal hf.continuous hfc _
  have hPg : ∀ k : ℤ, paperFT (EF.weilTest g g) (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) =
      ((lg k : ℝ) : ℂ) := fun k => paperFT_weilTest_self_ofReal hgc.continuous hgcs _
  -- The localizer does not increase any on-line term.
  have hlgf : ∀ k, lg k ≤ lf k := by
    intro k
    simp only [lg, lf]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    rw [hg, paperFT_sinePower hτ N hf hfs, norm_mul, norm_pow]
    have hs : ‖Complex.sin ((τ : ℂ) * (((k : ℝ) * (2 * π / L) : ℝ) : ℂ))‖ ≤ 1 := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_sin, Complex.norm_real]
      exact Real.abs_sin_le_one _
    calc _ ≤ 1 ^ N * ‖paperFT f (((k : ℝ) * (2 * π / L) : ℝ) : ℂ)‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hs N) (norm_nonneg _)
      _ = _ := by simp
  have hsumf := hasSum_two_norm_sq_lattice hL hf hfsL
  have hsumg := hasSum_two_norm_sq_lattice hL hgc hgsL
  have hD : HasSum (fun k : ℤ => 2 * lf k - 2 * lg k) (2 * L * Nf - 2 * L * Ng) := hsumf.sub hsumg
  have hDle : ∑ k ∈ S ∪ R, (2 * lf k - 2 * lg k) ≤ 2 * L * Nf - 2 * L * Ng :=
    sum_le_hasSum _ (fun k _ => by linarith only [hlgf k]) hD
  rw [Finset.sum_union hRS, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hDle
  -- Real forms of the two Weil forms.
  have hreal : ∀ h : ℝ → ℂ, (2 * (L : ℂ) * (∫ t, h t * conj (h t))).re =
      2 * L * ∫ t, ‖h t‖ ^ 2 := by
    intro h
    rw [integral_mul_conj_self_eq]
    rw [show ((2 : ℂ) * L * ((∫ t, ‖h t‖ ^ 2 : ℝ) : ℂ)) = ((2 * L * ∫ t, ‖h t‖ ^ 2 : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]
  have hmul : ∀ y : ℝ, ((2 : ℂ) * ((y : ℝ) : ℂ)).re = 2 * y := fun y => by simp
  let Pfm : ℤ → ℂ := fun k => paperFT (EF.weilTest f f) (((k : ℝ) * (2 * π / L) : ℝ) - I * d k)
  let Pfp : ℤ → ℂ := fun k => paperFT (EF.weilTest f f) (((k : ℝ) * (2 * π / L) : ℝ) + I * d k)
  let Pgm : ℤ → ℂ := fun k => paperFT (EF.weilTest g g) (((k : ℝ) * (2 * π / L) : ℝ) - I * d k)
  let Pgp : ℤ → ℂ := fun k => paperFT (EF.weilTest g g) (((k : ℝ) * (2 * π / L) : ℝ) + I * d k)
  have hWf : ((cutClusterConfig hL R S d hd0 hd2).W f f).re =
      2 * L * Nf + (∑ k ∈ S, ((Pfm k).re + (Pfp k).re) - ∑ k ∈ S, 2 * lf k) -
        ∑ k ∈ R, 2 * lf k := by
    rw [W_cutClusterConfig hL R S hRS d hd0 hd2 hf hfsL, Complex.sub_re, Complex.add_re, hreal,
      Complex.re_sum, Complex.re_sum, ← Finset.sum_sub_distrib]
    congr 2
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.sub_re, Complex.add_re, hPf, hmul]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [hPf, hmul]
  have hWg : ((SquareRootThreshold.clusterConfig hL S d hd0 hd2).W g g).re =
      2 * L * Ng + (∑ k ∈ S, ((Pgm k).re + (Pgp k).re) - ∑ k ∈ S, 2 * lg k) := by
    rw [W_clusterConfig hL S d hd0 hd2 hgc hgsL, Complex.add_re, hreal,
      Complex.re_sum, ← Finset.sum_sub_distrib]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.sub_re, Complex.add_re, hPg, hmul]
  -- The crystal floor for the localized test.
  have hfloorg := re_W_biquadraticCrystal_ge hL k₀ hM hδ0 hδ1 hA0 hA4 hgc hgs
  have hfl : 2 * L * (7 / 8) * Ng ≤ ((SquareRootThreshold.clusterConfig hL S d hd0 hd2).W g g).re := by
    refine le_trans ?_ hfloorg
    refine mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ?_ (by positivity)) hNg0
    linarith only [hfloor]
  -- The removed ordinates.
  have hRsum : ∑ k ∈ R, 2 * lg k ≤ L / 4 * Ng := by
    have hpt : ∀ k ∈ R, 2 * lg k ≤
        2 * ((r / Rr) ^ (2 * N) * (4 * A * Real.exp (2 * A * Rr))) * Ng := by
      intro k hk
      have h := norm_paperFT_sinePower_sq_le hτ N hf hfs hA0 hgs hr hrR (hlow k hk)
      have e : (r / Rr) ^ (2 * N) * (4 * A * Ng * Real.exp (2 * A * Rr)) =
          (r / Rr) ^ (2 * N) * (4 * A * Real.exp (2 * A * Rr)) * Ng := by ring
      simp only [lg]
      rw [← hg, ← hNg, e] at h
      linarith only [h]
    calc ∑ k ∈ R, 2 * lg k
        ≤ ∑ _k ∈ R, 2 * ((r / Rr) ^ (2 * N) * (4 * A * Real.exp (2 * A * Rr))) * Ng :=
          Finset.sum_le_sum hpt
      _ = (R.card : ℝ) * (2 * ((r / Rr) ^ (2 * N) * (4 * A * Real.exp (2 * A * Rr)))) * Ng := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ L / 4 * Ng := mul_le_mul_of_nonneg_right hlowsum hNg0
  -- The packet: off-line terms are unchanged up to a small error.
  obtain ⟨η, hη⟩ : ∃ η, η = 2 * (((2 * N : ℕ) : ℝ) * ρ ^ 2) := ⟨_, rfl⟩
  have hη12 : η ≤ 1 / 2 := by rw [hη]; linarith only [hρ2]
  have hη0 : 0 ≤ η := by rw [hη]; positivity
  have herr : ∀ k ∈ S, ∀ y : ℝ, |y| ≤ δ →
      (paperFT (EF.weilTest g g) (((k : ℝ) * (2 * π / L) : ℝ) + I * y)).re -
          2 * η * (4 * A * Real.exp (2 * A * δ)) * Ng ≤
        (paperFT (EF.weilTest f f) (((k : ℝ) * (2 * π / L) : ℝ) + I * y)).re := by
    intro k hk y hy
    obtain ⟨z, hz⟩ : ∃ z : ℂ, z = (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) + I * y := ⟨_, rfl⟩
    rw [← hz]
    have hw : ‖(τ : ℂ) * (z - T)‖ ≤ ρ := by rw [hz]; exact hnear k hk y hy
    have hw2 : ‖(τ : ℂ) * (z - T)‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    have hm0 : (0 : ℝ) ≤ ((2 * N : ℕ) : ℝ) := Nat.cast_nonneg _
    have hmw : ((2 * N : ℕ) : ℝ) * ‖(τ : ℂ) * (z - T)‖ ^ 2 ≤ ((2 * N : ℕ) : ℝ) * ρ ^ 2 :=
      mul_le_mul_of_nonneg_left hw2 hm0
    have hμ := norm_one_sub_sin_pow_le (m := 2 * N) hτT (z := z) (hw.trans hρ1)
      (by linarith only [hmw, hρ2])
    obtain ⟨μ, hμd⟩ : ∃ μ, μ = Complex.sin (τ * z) ^ (2 * N) := ⟨_, rfl⟩
    rw [← hμd] at hμ
    have hμη : ‖1 - μ‖ ≤ η := by rw [hη]; linarith only [hμ, hmw]
    have hPgz : paperFT (EF.weilTest g g) z = μ * paperFT (EF.weilTest f f) z := by
      rw [hg, paperFT_weilTest_sinePower hτ N hf hfs, hμd]
    have hμ12 : 1 / 2 ≤ ‖μ‖ := by
      have h := norm_sub_norm_le (1 : ℂ) (1 - μ)
      have h1 : ‖(1 : ℂ) - (1 - μ)‖ = ‖μ‖ := by simp
      rw [h1, norm_one] at h
      linarith only [h, hμη, hη12]
    have hPfle : ‖paperFT (EF.weilTest f f) z‖ ≤ 2 * ‖paperFT (EF.weilTest g g) z‖ := by
      rw [hPgz, norm_mul]
      have := mul_le_mul_of_nonneg_right hμ12 (norm_nonneg (paperFT (EF.weilTest f f) z))
      linarith only [this]
    have him : |z.im| ≤ δ := by
      rw [hz]
      simpa using hy
    have hPgle : ‖paperFT (EF.weilTest g g) z‖ ≤ 4 * A * Ng * Real.exp (2 * A * δ) := by
      refine (norm_paperFT_weilTest_le hgc.continuous hA0 hgs z).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      exact mul_le_mul_of_nonneg_left him (by positivity)
    have hdiff : ‖paperFT (EF.weilTest f f) z - paperFT (EF.weilTest g g) z‖ ≤
        2 * η * (4 * A * Real.exp (2 * A * δ)) * Ng := by
      have e : paperFT (EF.weilTest f f) z - paperFT (EF.weilTest g g) z =
          (1 - μ) * paperFT (EF.weilTest f f) z := by rw [hPgz]; ring
      rw [e, norm_mul]
      calc ‖1 - μ‖ * ‖paperFT (EF.weilTest f f) z‖
          ≤ η * (2 * (4 * A * Ng * Real.exp (2 * A * δ))) :=
            mul_le_mul hμη (hPfle.trans (by linarith only [hPgle])) (norm_nonneg _) hη0
        _ = _ := by ring
    have hre := Complex.abs_re_le_norm
      (paperFT (EF.weilTest f f) z - paperFT (EF.weilTest g g) z)
    rw [Complex.sub_re] at hre
    linarith only [hre, hdiff, neg_abs_le ((paperFT (EF.weilTest f f) z).re -
      (paperFT (EF.weilTest g g) z).re)]
  have hSsum : ∑ k ∈ S, ((Pgm k).re + (Pgp k).re) - L / 4 * Ng ≤
      ∑ k ∈ S, ((Pfm k).re + (Pfp k).re) := by
    have hpt : ∀ k ∈ S, (Pgm k).re + (Pgp k).re -
        2 * (2 * η * (4 * A * Real.exp (2 * A * δ))) * Ng ≤ (Pfm k).re + (Pfp k).re := by
      intro k hk
      have hdk : |d k| ≤ δ := by
        rw [abs_of_pos (hd0 k hk)]
        exact hd1 k hk
      have h1 := herr k hk (-d k) (by rwa [abs_neg])
      have h2 := herr k hk (d k) hdk
      have e : (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) + I * ((-d k : ℝ) : ℂ) =
          (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) - I * (d k : ℂ) := by push_cast; ring
      rw [e] at h1
      simp only [Pgm, Pgp, Pfm, Pfp]
      linarith only [h1, h2]
    have hsum : ∑ k ∈ S, ((Pgm k).re + (Pgp k).re) -
        (S.card : ℝ) * (2 * (2 * η * (4 * A * Real.exp (2 * A * δ)))) * Ng ≤
        ∑ k ∈ S, ((Pfm k).re + (Pfp k).re) := by
      have h := Finset.sum_le_sum hpt
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h
      linarith only [h]
    have hcard : (S.card : ℝ) * (2 * (2 * η * (4 * A * Real.exp (2 * A * δ)))) * Ng ≤ L / 4 * Ng := by
      refine mul_le_mul_of_nonneg_right ?_ hNg0
      rw [hη]
      exact hnearsum
    linarith only [hsum, hcard]
  have hLNg : 0 ≤ L * Ng := mul_nonneg hL.le hNg0
  rw [hWf]
  linarith only [hWg, hfl, hRsum, hSsum, hDle, hLNg]

end GaloisForLFunctions.WindowVisibilityLaw
