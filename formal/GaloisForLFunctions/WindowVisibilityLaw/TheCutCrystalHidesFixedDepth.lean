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
    have h1 : ∑ k ∈ S, (paperFT (EF.weilTest f f) ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) - I * d k) +
        paperFT (EF.weilTest f f) ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) + I * d k) -
        2 * paperFT (EF.weilTest f f) (((k : ℝ) * (2 * π / L) : ℝ) : ℂ)).re =
        ∑ k ∈ S, (((Pfm k).re + (Pfp k).re) - 2 * lf k) :=
      Finset.sum_congr rfl fun k _ => by rw [Complex.sub_re, Complex.add_re, hPf, hmul]
    have h2 : ∑ k ∈ R, (2 * paperFT (EF.weilTest f f) (((k : ℝ) * (2 * π / L) : ℝ) : ℂ)).re =
        ∑ k ∈ R, 2 * lf k :=
      Finset.sum_congr rfl fun k _ => by rw [hPf, hmul]
    rw [W_cutClusterConfig hL R S hRS d hd0 hd2 hf hfsL, Complex.sub_re, Complex.add_re, hreal,
      Complex.re_sum, Complex.re_sum, h1, h2, Finset.sum_sub_distrib]
  have hWg : ((SquareRootThreshold.clusterConfig hL S d hd0 hd2).W g g).re =
      2 * L * Ng + (∑ k ∈ S, ((Pgm k).re + (Pgp k).re) - ∑ k ∈ S, 2 * lg k) := by
    have h1 : ∑ k ∈ S, (paperFT (EF.weilTest g g) ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) - I * d k) +
        paperFT (EF.weilTest g g) ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) + I * d k) -
        2 * paperFT (EF.weilTest g g) (((k : ℝ) * (2 * π / L) : ℝ) : ℂ)).re =
        ∑ k ∈ S, (((Pgm k).re + (Pgp k).re) - 2 * lg k) :=
      Finset.sum_congr rfl fun k _ => by rw [Complex.sub_re, Complex.add_re, hPg, hmul]
    rw [W_clusterConfig hL S d hd0 hd2 hgc hgsL, Complex.add_re, hreal,
      Complex.re_sum, h1, Finset.sum_sub_distrib]
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

/-- A cut cluster is tempered: it is a part of the full cluster with the same multiplicities. -/
theorem temperedConfig_cutClusterConfig {L : ℝ} (hL : 0 < L) (R S : Finset ℤ) (d : ℤ → ℝ)
    (hd0 : ∀ k ∈ S, 0 < d k) (hd1 : ∀ k ∈ S, d k ≤ 1 / 2) :
    TemperedConfig (cutClusterConfig hL R S d hd0 hd1) := by
  have h := temperedConfig_clusterConfig hL S d hd0 hd1
  have hsub : ∀ ρ ∈ (cutClusterConfig hL R S d hd0 hd1).carrier,
      ρ ∈ (SquareRootThreshold.clusterConfig hL S d hd0 hd1).carrier := by
    rintro _ ((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩)
    · exact Or.inl (Or.inl ⟨⟨k, fun hk => k.2 (Finset.mem_union_left _ hk)⟩, rfl⟩)
    · exact Or.inl (Or.inr ⟨k, rfl⟩)
    · exact Or.inr ⟨k, rfl⟩
  let ι : (cutClusterConfig hL R S d hd0 hd1).carrier →
      (SquareRootThreshold.clusterConfig hL S d hd0 hd1).carrier := fun ρ => ⟨ρ, hsub ρ ρ.2⟩
  have hinj : Function.Injective ι := fun a b hab =>
    Subtype.ext (congrArg (fun x : (SquareRootThreshold.clusterConfig hL S d hd0 hd1).carrier =>
      (x : ℂ)) hab)
  have hm : ∀ ρ : ℂ, (cutClusterConfig hL R S d hd0 hd1).mult ρ =
      (SquareRootThreshold.clusterConfig hL S d hd0 hd1).mult ρ := fun _ => rfl
  have h' : Summable fun ρ : (SquareRootThreshold.clusterConfig hL S d hd0 hd1).carrier =>
      ((SquareRootThreshold.clusterConfig hL S d hd0 hd1).mult ρ : ℝ) /
        (1 + Complex.normSq (gammaOf ρ)) := h
  refine Summable.congr (h'.comp_injective hinj) fun ρ => ?_
  simp only [Function.comp_apply, ι]
  rw [hm]

/-- **The uniform local count of the cut cluster.** If every kept ordinate lies above `t₀`, and
`t₀` pays the lattice density, then `N(t,t+1] ≤ 2 log(|t|+3)` at every height. -/
theorem cutCluster_local_count {L t₀ : ℝ} (hL : 0 < L) (ht₀ : 0 < t₀) (R S : Finset ℤ)
    (hRS : Disjoint S R) (d : ℤ → ℝ) (hd0 : ∀ k ∈ S, 0 < d k) (hd1 : ∀ k ∈ S, d k ≤ 1 / 2)
    (hfar : ∀ k : ℤ, k ∉ R → t₀ ≤ |(k : ℝ) * (2 * π / L)|)
    (hcount : 6 * (L / (2 * π) + 1) ≤ 2 * Real.log t₀) (t : ℝ) :
    ((cutClusterConfig hL R S d hd0 hd1).N t (t + 1) : ℝ) ≤ 2 * Real.log (|t| + 3) := by
  classical
  set Z := cutClusterConfig hL R S d hd0 hd1 with hZ
  have hfin : (Z.window t (t + 1)).Finite := Z.finite_window t (t + 1)
  have hlog0 : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith only [abs_nonneg t])
  rcases (Z.window t (t + 1)).eq_empty_or_nonempty with hE | ⟨ρ₀, hρ₀⟩
  · unfold ZeroConfig.N
    rw [hE, finsum_mem_empty]
    simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlog0
  have hπ0 : 0 < 2 * π / L := by positivity
  -- Some kept ordinate lies in the window, so the height is above the cut.
  have hkept : ∃ k : ℤ, k ∉ R ∧ ρ₀.im = (k : ℝ) * (2 * π / L) := by
    obtain ⟨hc, -⟩ := hρ₀
    rcases hc with (⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩
    · exact ⟨k, fun h => k.2 (Finset.mem_union_right _ h), rfl⟩
    · exact ⟨k, Finset.disjoint_left.mp hRS k.2, rfl⟩
    · exact ⟨k, Finset.disjoint_left.mp hRS k.2, rfl⟩
  obtain ⟨k', hk'R, hk'im⟩ := hkept
  have hρ₀t : t < ρ₀.im ∧ ρ₀.im ≤ t + 1 := hρ₀.2
  have hlogt : Real.log t₀ ≤ Real.log (|t| + 3) := by
    refine Real.log_le_log ht₀ ((hfar k' hk'R).trans ?_)
    rw [← hk'im, abs_le]
    constructor
    · linarith only [hρ₀t.1, neg_abs_le t, abs_nonneg t]
    · linarith only [hρ₀t.2, le_abs_self t, abs_nonneg t]
  -- Count the ordinates in the window.
  obtain ⟨c, hc⟩ : ∃ c, c = L / (2 * π) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  have hcinv : 2 * π / L = c⁻¹ := by rw [hc, inv_div]
  let K : Finset ℤ := Finset.Ioc ⌊t * c⌋ ⌊(t + 1) * c⌋
  have hKmem : ∀ k : ℤ, t < (k : ℝ) * (2 * π / L) → (k : ℝ) * (2 * π / L) ≤ t + 1 → k ∈ K := by
    intro k h1 h2
    rw [hcinv, ← div_eq_mul_inv] at h1 h2
    rw [lt_div_iff₀ hc0] at h1
    rw [div_le_iff₀ hc0] at h2
    exact Finset.mem_Ioc.mpr ⟨Int.floor_lt.mpr h1, Int.le_floor.mpr h2⟩
  have hKcard : (K.card : ℝ) ≤ c + 1 := by
    have hb : ((⌊(t + 1) * c⌋ : ℤ) : ℝ) ≤ (t + 1) * c := Int.floor_le _
    have ha : t * c < ((⌊t * c⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    simp only [K]
    rw [Int.card_Ioc]
    rcases le_total ⌊t * c⌋ ⌊(t + 1) * c⌋ with hab | hab
    · have hcast : ((⌊(t + 1) * c⌋ - ⌊t * c⌋).toNat : ℝ) =
          ((⌊(t + 1) * c⌋ : ℤ) : ℝ) - ((⌊t * c⌋ : ℤ) : ℝ) := by
        have h0 : ((⌊(t + 1) * c⌋ - ⌊t * c⌋).toNat : ℤ) = ⌊(t + 1) * c⌋ - ⌊t * c⌋ :=
          Int.toNat_of_nonneg (by omega)
        exact_mod_cast h0
      rw [hcast]
      nlinarith only [hb, ha]
    · have h0 : (⌊(t + 1) * c⌋ - ⌊t * c⌋).toNat = 0 := Int.toNat_of_nonpos (by omega)
      rw [h0]
      push_cast
      linarith only [hc0]
  let on : ℤ → ℂ := verticalLatticePoint L 0
  let pp : ℤ → ℂ := fun k => verticalLatticePoint L (d k) k
  let pm : ℤ → ℂ := fun k => verticalLatticePoint L (-d k) k
  have hsub : hfin.toFinset ⊆ K.image on ∪ K.image pp ∪ K.image pm := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    obtain ⟨hc', h1, h2⟩ := hρ
    rcases hc' with (⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨k, hKmem k h1 h2, rfl⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨k, hKmem k h1 h2, rfl⟩))
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, hKmem k h1 h2, rfl⟩)
  have hcard : (hfin.toFinset.card : ℝ) ≤ 3 * (K.card : ℝ) := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (K.image on ∪ K.image pp) (K.image pm)
    have h3 := Finset.card_union_le (K.image on) (K.image pp)
    have h4 : (K.image on).card ≤ K.card := Finset.card_image_le
    have h5 : (K.image pp).card ≤ K.card := Finset.card_image_le
    have h6 : (K.image pm).card ≤ K.card := Finset.card_image_le
    have : hfin.toFinset.card ≤ 3 * K.card := by omega
    exact_mod_cast this
  have hN : Z.N t (t + 1) = ∑ ρ ∈ hfin.toFinset, Z.mult ρ := by
    rw [ZeroConfig.N]
    exact finsum_mem_eq_finite_toFinset_sum _ hfin
  have hmult : ∀ ρ, Z.mult ρ ≤ 2 := fun ρ => by
    change (if ρ.re = 1 / 2 then 2 else 1) ≤ 2
    split_ifs <;> norm_num
  have hNle : (Z.N t (t + 1) : ℝ) ≤ 2 * (hfin.toFinset.card : ℝ) := by
    rw [hN]
    have h : ∑ ρ ∈ hfin.toFinset, Z.mult ρ ≤ hfin.toFinset.card * 2 :=
      Finset.sum_le_card_nsmul _ _ _ (fun ρ _ => hmult ρ)
    have h' : ((∑ ρ ∈ hfin.toFinset, Z.mult ρ : ℕ) : ℝ) ≤ ((hfin.toFinset.card * 2 : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h' ⊢
    linarith only [h']
  rw [← hc] at hcount
  linarith only [hNle, hcard, hKcard, hcount, hlogt]

/-- **A fixed depth hides from logarithmic aperture under a uniform local count.** For every depth
`0 < δ ≤ ½` and height `T ≥ e³⁶⁰` there is a configuration with `N(t,t+1] ≤ 2 log(|t|+3)` at every
height and finitely many off-line zeros, containing a zero of depth `δ` at ordinate `T`, which is
window-positive at aperture `(log T)/36`. -/
theorem exists_hidden_fixed_depth_zero_at_logarithmic_aperture {δ T : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 2) (hT : Real.exp 360 ≤ T) :
    ∃ Z : ZeroConfig, TemperedConfig Z ∧
      (∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ 2 * Real.log (|t| + 3)) ∧
      (∃ ρ ∈ Z.carrier, ρ.re = 1 / 2 + δ ∧ ρ.im = T) ∧
      {ρ ∈ Z.carrier | ρ.re ≠ 1 / 2}.Finite ∧
      WindowPositiveAt Z (Real.log T / 36) := by
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  have hT0 : 0 < T := (Real.exp_pos _).trans_le hT
  obtain ⟨a, ha⟩ : ∃ a, a = Real.log T / 36 := ⟨_, rfl⟩
  rw [← ha]
  have hlogT : 360 ≤ Real.log T := (Real.le_log_iff_exp_le hT0).mpr hT
  have ha10 : 10 ≤ a := by rw [ha]; linarith only [hlogT]
  have ha0 : 0 < a := by linarith only [ha10]
  obtain ⟨E, hEd⟩ : ∃ E, E = Real.exp a := ⟨_, rfl⟩
  have hEa : a ≤ E := by rw [hEd]; linarith only [Real.add_one_le_exp a]
  have hE : 20000 ≤ E := by
    have h10 : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    have h27 : (2.7 : ℝ) ^ 10 ≤ Real.exp 1 ^ 10 :=
      pow_le_pow_left₀ (by norm_num) (by linarith only [Real.exp_one_gt_d9]) 10
    have h1 : Real.exp 10 ≤ E := by rw [hEd]; exact Real.exp_le_exp.mpr ha10
    have h2 : (20000 : ℝ) ≤ (2.7 : ℝ) ^ 10 := by norm_num
    linarith only [h10, h27, h1, h2]
  have hE1 : 1 ≤ E := by linarith only [hE]
  have hE0 : 0 < E := by linarith only [hE]
  have hpow : ∀ {m n : ℕ}, m ≤ n → E ^ m ≤ E ^ n := fun h => pow_le_pow_right₀ hE1 h
  have hEpow : ∀ m : ℕ, Real.exp ((m : ℝ) * a) = E ^ m := fun m => by
    rw [hEd, Real.exp_nat_mul]
  have hTE : T = E ^ 36 := by
    rw [← hEpow]
    have h : ((36 : ℕ) : ℝ) * a = Real.log T := by rw [ha]; push_cast; ring
    rw [h, Real.exp_log hT0]
  -- The lattice: density between `16a` and `17a`, with `T` on the lattice.
  have hT36 : (E ^ 36 : ℝ) = T := hTE.symm
  have hT7 : 7 ≤ T := by
    rw [hTE]
    have := hpow (show 1 ≤ 36 by norm_num)
    linarith only [this, hE, pow_one E]
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℤ, k₀ = ⌈16 * a * T / (2 * π)⌉ := ⟨_, rfl⟩
  have hk₀le : 16 * a * T / (2 * π) ≤ (k₀ : ℝ) := by rw [hk₀]; exact Int.le_ceil _
  have hk₀lt : (k₀ : ℝ) < 16 * a * T / (2 * π) + 1 := by rw [hk₀]; exact Int.ceil_lt_add_one _
  have h2π : 0 < 2 * π := by positivity
  have hk₀T : T ≤ (k₀ : ℝ) := by
    refine le_trans ?_ hk₀le
    rw [le_div_iff₀ h2π]
    nlinarith only [ha10, hT0, hpi4]
  have hk₀pos : (0 : ℝ) < k₀ := hT0.trans_le hk₀T
  obtain ⟨L, hLd⟩ : ∃ L, L = 2 * π * k₀ / T := ⟨_, rfl⟩
  have hL16 : 16 * a ≤ L := by
    rw [hLd, le_div_iff₀ hT0]
    rw [div_le_iff₀ h2π] at hk₀le
    linarith only [hk₀le]
  have hL17 : L ≤ 17 * a := by
    rw [hLd, div_le_iff₀ hT0]
    have h1 : (k₀ : ℝ) * (2 * π) < 16 * a * T + 2 * π := by
      have := mul_lt_mul_of_pos_right hk₀lt h2π
      rw [add_mul, one_mul, div_mul_cancel₀ _ h2π.ne'] at this
      exact this
    nlinarith only [h1, ha10, hT7, hpi4]
  have hL0 : 0 < L := by linarith only [hL16, ha0]
  have hx0 : (k₀ : ℝ) * (2 * π / L) = T := by
    rw [hLd]
    field_simp
  have hgap : 2 * π / L ≤ 1 := by
    rw [div_le_one hL0]
    linarith only [hL16, ha10, hpi4]
  have hgap0 : 0 < 2 * π / L := by positivity
  -- The cut.
  obtain ⟨t₀, ht₀d⟩ : ∃ t₀, t₀ = Real.exp L := ⟨_, rfl⟩
  have ht₀0 : 0 < t₀ := by rw [ht₀d]; exact Real.exp_pos _
  have ht₀E : t₀ ≤ E ^ 17 := by
    rw [ht₀d, ← hEpow]
    exact Real.exp_le_exp.mpr (by push_cast; linarith only [hL17])
  have ht₀1 : 1 ≤ t₀ := by
    rw [ht₀d]
    exact Real.one_le_exp hL0.le
  obtain ⟨k₁, hk₁⟩ : ∃ k₁ : ℕ, k₁ = ⌈t₀ * (L / (2 * π))⌉₊ + 1 := ⟨_, rfl⟩
  have hLdiv : 0 < L / (2 * π) := by positivity
  have hk₁ge : t₀ * (L / (2 * π)) ≤ (k₁ : ℝ) := by
    rw [hk₁]
    push_cast
    linarith only [Nat.le_ceil (t₀ * (L / (2 * π)))]
  have hk₁le : (k₁ : ℝ) ≤ t₀ * (L / (2 * π)) + 2 := by
    rw [hk₁]
    push_cast
    linarith only [Nat.ceil_lt_add_one (show 0 ≤ t₀ * (L / (2 * π)) by positivity)]
  have hdivmul : (L / (2 * π)) * (2 * π / L) = 1 := by field_simp
  let R : Finset ℤ := Finset.Ioo (-(k₁ : ℤ)) (k₁ : ℤ)
  -- The packet.
  obtain ⟨M, hMd⟩ : ∃ M : ℕ, M = ⌈2584 * a ^ 2 * E ^ 2⌉₊ := ⟨_, rfl⟩
  have hE2 : Real.exp (2 * a) = E ^ 2 := by simpa using hEpow 2
  have hMge : 2584 * a ^ 2 * E ^ 2 ≤ (M : ℝ) := by rw [hMd]; exact Nat.le_ceil _
  have hMle : (M : ℝ) + 1 ≤ E ^ 6 := by
    have h1 : (M : ℝ) < 2584 * a ^ 2 * E ^ 2 + 1 := by
      rw [hMd]; exact Nat.ceil_lt_add_one (by positivity)
    have ha2 : a ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ ha0.le hEa 2
    have h2 : 2584 * a ^ 2 * E ^ 2 + 2 ≤ E * E ^ 2 * E ^ 2 + E ^ 5 := by
      have h3 : 2584 * a ^ 2 * E ^ 2 ≤ E * E ^ 2 * E ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (by linarith only [hE]) ha2 (by positivity) hE0.le) (by positivity)
      have h4 : (2 : ℝ) ≤ E ^ 5 := by
        have := hpow (show 1 ≤ 5 by norm_num)
        linarith only [this, hE, pow_one E]
      linarith only [h3, h4]
    have h5 : E * E ^ 2 * E ^ 2 + E ^ 5 ≤ E ^ 6 := by
      have e : E * E ^ 2 * E ^ 2 + E ^ 5 = 2 * E ^ 5 := by ring
      have h6 : 2 * E ^ 5 ≤ E * E ^ 5 :=
        mul_le_mul_of_nonneg_right (by linarith only [hE]) (by positivity)
      rw [e]
      calc 2 * E ^ 5 ≤ E * E ^ 5 := h6
        _ = E ^ 6 := by ring
    linarith only [h1, h2, h5]
  have hM2 : 2 ≤ M := by
    have h : (2 : ℝ) ≤ (M : ℝ) := by
      refine le_trans ?_ hMge
      have ha1 : 1 ≤ a ^ 2 := one_le_pow₀ (by linarith only [ha10])
      have hE1' : 1 ≤ E ^ 2 := one_le_pow₀ hE1
      nlinarith only [mul_le_mul ha1 hE1' (by norm_num) (by positivity)]
    exact_mod_cast h
  have hS : Disjoint (taperedSupport k₀ M) R := by
    rw [Finset.disjoint_left]
    intro k hk hkR
    rw [mem_taperedSupport_iff, abs_lt] at hk
    have hk' := (Finset.mem_Ioo.mp hkR).2
    have hint : k₀ - (M : ℤ) < k := by omega
    have hgt : (k₁ : ℤ) ≤ k₀ - (M : ℤ) := by
      have hreal : (k₁ : ℝ) + M ≤ k₀ := by
        have hk₁E : (k₁ : ℝ) ≤ E ^ 20 := by
          refine hk₁le.trans ?_
          have hdiv : L / (2 * π) ≤ 17 * a := by
            rw [div_le_iff₀ h2π]
            nlinarith only [hL17, ha10, hpi3]
          have h1 : t₀ * (L / (2 * π)) ≤ E ^ 17 * (17 * E) :=
            mul_le_mul ht₀E (by linarith only [hdiv, hEa]) hLdiv.le (by positivity)
          have h2 : E ^ 17 * (17 * E) + 2 ≤ E ^ 17 * E * E + E ^ 19 := by
            have h3 : E ^ 17 * (17 * E) ≤ E ^ 17 * E * E := by
              have : 17 * E ≤ E * E := mul_le_mul_of_nonneg_right (by linarith only [hE]) hE0.le
              calc E ^ 17 * (17 * E) ≤ E ^ 17 * (E * E) := by gcongr
                _ = _ := by ring
            have h4 : (2 : ℝ) ≤ E ^ 19 := by
              have := hpow (show 1 ≤ 19 by norm_num)
              linarith only [this, hE, pow_one E]
            linarith only [h3, h4]
          have h5 : E ^ 17 * E * E + E ^ 19 ≤ E ^ 20 := by
            have e : E ^ 17 * E * E + E ^ 19 = 2 * E ^ 19 := by ring
            rw [e]
            calc 2 * E ^ 19 ≤ E * E ^ 19 :=
                  mul_le_mul_of_nonneg_right (by linarith only [hE]) (by positivity)
              _ = E ^ 20 := by ring
          linarith only [h1, h2, h5]
        have h6 : E ^ 20 + E ^ 6 ≤ T := by
          rw [hTE]
          have h7 := hpow (show 6 ≤ 20 by norm_num)
          have h8 := hpow (show 21 ≤ 36 by norm_num)
          have h9 : 2 * E ^ 20 ≤ E ^ 21 := by
            calc 2 * E ^ 20 ≤ E * E ^ 20 :=
                  mul_le_mul_of_nonneg_right (by linarith only [hE]) (by positivity)
              _ = E ^ 21 := by ring
          linarith only [h7, h8, h9]
        linarith only [hk₁E, hMle, h6, hk₀T]
      have : ((k₁ : ℤ) : ℝ) ≤ ((k₀ - (M : ℤ) : ℤ) : ℝ) := by
        push_cast
        linarith only [hreal]
      exact_mod_cast this
    omega
  -- The localizer.
  obtain ⟨τ, hτd⟩ : ∃ τ, τ = π / (2 * T) := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by rw [hτd]; positivity
  have hτT : τ * T = π / 2 := by rw [hτd]; field_simp
  have hτE : τ * E ^ 36 ≤ 2 := by rw [hT36, hτT]; linarith only [hpi4]
  obtain ⟨N, hNd⟩ : ∃ N : ℕ, N = ⌈13 * a * t₀⌉₊ := ⟨_, rfl⟩
  have hNge : 13 * a * t₀ ≤ (N : ℝ) := by rw [hNd]; exact Nat.le_ceil _
  have hNle : (N : ℝ) ≤ E ^ 19 := by
    have h1 : (N : ℝ) < 13 * a * t₀ + 1 := by rw [hNd]; exact Nat.ceil_lt_add_one (by positivity)
    have h2 : 13 * a * t₀ ≤ 13 * E * E ^ 17 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hEa (by norm_num)) ht₀E ht₀0.le (by positivity)
    have h3 : 13 * E * E ^ 17 + 1 ≤ E ^ 19 := by
      have e : 13 * E * E ^ 17 = 13 * E ^ 18 := by ring
      have e' : E ^ 19 = E * E ^ 18 := by ring
      have h4 : (1 : ℝ) ≤ E ^ 18 := one_le_pow₀ hE1
      rw [e, e']
      nlinarith only [hE, h4]
    linarith only [h1, h2, h3]
  have hNτ : (N : ℝ) * τ ≤ a := by
    have h1 : (N : ℝ) * τ * E ^ 36 ≤ E ^ 19 * 2 := by
      rw [mul_assoc]
      exact mul_le_mul hNle hτE (by positivity) (by positivity)
    have h2 : E ^ 19 * 2 ≤ E ^ 36 := by
      have h3 := hpow (show 20 ≤ 36 by norm_num)
      have h4 : E ^ 19 * 2 ≤ E ^ 19 * E := mul_le_mul_of_nonneg_left (by linarith only [hE])
        (by positivity)
      have e : E ^ 19 * E = E ^ 20 := by ring
      linarith only [h3, h4, e]
    have h3 : (N : ℝ) * τ ≤ 1 := by
      have h36 : (0 : ℝ) < E ^ 36 := by positivity
      refine le_of_mul_le_mul_right ?_ h36
      linarith only [h1, h2]
    linarith only [h3, ha10]
  have hNτ0 : 0 ≤ (N : ℝ) * τ := by positivity
  obtain ⟨A, hAd⟩ : ∃ A, A = a + (N : ℝ) * τ := ⟨_, rfl⟩
  have hA2 : A ≤ 2 * a := by rw [hAd]; linarith only [hNτ]
  have hA0 : 0 ≤ A := by rw [hAd]; linarith only [hNτ0, ha0]
  have hA4 : 4 * (a + N * τ) ≤ L := by rw [← hAd]; linarith only [hA2, hL16, ha0]
  -- Tapering.
  have hfloor : 38 * (a + N * τ) * L * δ ^ 2 * Real.cosh (2 * δ * (a + N * τ)) / (M : ℝ) ≤ 1 / 8 := by
    rw [← hAd]
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    rw [div_le_iff₀ hM0]
    have hδ2 : δ ^ 2 ≤ 1 / 4 := by nlinarith only [hδ0, hδ1]
    have hcosh : Real.cosh (2 * δ * A) ≤ E ^ 2 := by
      have hy0 : 0 ≤ 2 * δ * A := by positivity
      have hy : 2 * δ * A ≤ 2 * a := by nlinarith only [hδ0, hδ1, hA0, hA2]
      rw [← hE2]
      refine le_trans ?_ (Real.exp_le_exp.mpr hy)
      rw [Real.cosh_eq]
      have : Real.exp (-(2 * δ * A)) ≤ Real.exp (2 * δ * A) := Real.exp_le_exp.mpr (by linarith only [hy0])
      linarith only [this]
    have hcosh0 : 0 ≤ Real.cosh (2 * δ * A) := (Real.cosh_pos _).le
    have h1 : A * L ≤ (2 * a) * (17 * a) := mul_le_mul hA2 hL17 hL0.le (by positivity)
    have h2 : (A * L) * δ ^ 2 ≤ ((2 * a) * (17 * a)) * (1 / 4) :=
      mul_le_mul h1 hδ2 (sq_nonneg _) (by positivity)
    have h3 : (A * L * δ ^ 2) * Real.cosh (2 * δ * A) ≤ (((2 * a) * (17 * a)) * (1 / 4)) * E ^ 2 :=
      mul_le_mul h2 hcosh hcosh0 (by positivity)
    have e : 38 * A * L * δ ^ 2 * Real.cosh (2 * δ * A) =
        38 * ((A * L * δ ^ 2) * Real.cosh (2 * δ * A)) := by ring
    rw [e]
    have e2 : 1 / 8 * (2584 * a ^ 2 * E ^ 2) = 38 * ((((2 * a) * (17 * a)) * (1 / 4)) * E ^ 2) := by
      ring
    have h4 := mul_le_mul_of_nonneg_left hMge (show (0 : ℝ) ≤ 1 / 8 by norm_num)
    linarith only [h3, h4, e2]
  -- The removed points.
  obtain ⟨r, hrd⟩ : ∃ r, r = 2 * t₀ := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrd]; positivity
  obtain ⟨Rr, hRrd⟩ : ∃ Rr, Rr = Real.exp 1 * r := ⟨_, rfl⟩
  have hrR : r ≤ Rr := by
    rw [hRrd]
    have := Real.add_one_le_exp (1 : ℝ)
    nlinarith only [this, hr0]
  have hlow : ∀ k ∈ R, |(k : ℝ) * (2 * π / L)| ≤ r := by
    intro k hk
    obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hk
    have hkabs : (|k| : ℤ) ≤ (k₁ : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
    have hkabs' : |(k : ℝ)| ≤ (k₁ : ℝ) := by exact_mod_cast hkabs
    rw [abs_mul, abs_of_pos hgap0]
    have h3 : |(k : ℝ)| * (2 * π / L) ≤ (t₀ * (L / (2 * π)) + 2) * (2 * π / L) :=
      mul_le_mul_of_nonneg_right (hkabs'.trans hk₁le) hgap0.le
    have e : (t₀ * (L / (2 * π)) + 2) * (2 * π / L) =
        t₀ * ((L / (2 * π)) * (2 * π / L)) + 2 * (2 * π / L) := by ring
    rw [e, hdivmul] at h3
    rw [hrd]
    have hg : 2 * (2 * π / L) ≤ 1 := by
      rw [show 2 * (2 * π / L) = 4 * π / L by ring, div_le_one hL0]
      linarith only [hL16, ha10, hpi4]
    linarith only [h3, hg, ht₀1]
  have hRcard : (R.card : ℝ) ≤ t₀ * L := by
    have hcard : R.card ≤ 2 * k₁ := by
      simp only [R]
      rw [Int.card_Ioo]
      omega
    have hc : (R.card : ℝ) ≤ 2 * (k₁ : ℝ) := by exact_mod_cast hcard
    have hdiv : 2 * (L / (2 * π)) ≤ L / 3 := by
      rw [show 2 * (L / (2 * π)) = L / π by field_simp]
      exact div_le_div_of_nonneg_left hL0.le (by norm_num) hpi3.le
    have h1 : 2 * (t₀ * (L / (2 * π))) ≤ t₀ * (L / 3) := by
      calc 2 * (t₀ * (L / (2 * π))) = t₀ * (2 * (L / (2 * π))) := by ring
        _ ≤ t₀ * (L / 3) := mul_le_mul_of_nonneg_left hdiv ht₀0.le
    have h2 : 4 ≤ t₀ * L * (2 / 3) := by
      have : (1 : ℝ) * 160 ≤ t₀ * L := mul_le_mul ht₀1 (by linarith only [hL16, ha10]) (by norm_num)
        ht₀0.le
      linarith only [this]
    nlinarith only [hc, hk₁le, h1, h2]
  have hlowsum : (R.card : ℝ) * (2 * ((r / Rr) ^ (2 * N) *
      (4 * (a + N * τ) * Real.exp (2 * (a + N * τ) * Rr)))) ≤ L / 4 := by
    rw [← hAd]
    obtain ⟨x, hxd⟩ : ∃ x, x = a * t₀ := ⟨_, rfl⟩
    have ht₀4 : 4 ≤ t₀ := by
      rw [ht₀d]
      linarith only [Real.add_one_le_exp L, hL16, ha10]
    have hx32 : 32 ≤ x := by
      rw [hxd]
      nlinarith only [ha10, ht₀4]
    have hRr0 : 0 < Rr := hr0.trans_le hrR
    have hx0 : 0 < x := by linarith only [hx32]
    -- The ratio pays the circle bound.
    have hratio : r / Rr = Real.exp (-1) := by
      rw [hRrd, div_mul_eq_div_div_swap, div_self hr0.ne', Real.exp_neg]
      simp
    have hprod : (r / Rr) ^ (2 * N) * Real.exp (2 * A * Rr) ≤ Real.exp (-(2 * x)) := by
      rw [hratio, ← Real.exp_nat_mul, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hN2 : ((2 * N : ℕ) : ℝ) * (-1) = -(2 * (N : ℝ)) := by push_cast; ring
      rw [hN2]
      have hRr6 : Rr ≤ 6 * t₀ := by
        rw [hRrd, hrd]
        nlinarith only [Real.exp_one_lt_d9, ht₀0]
      have h4A : 2 * A * Rr ≤ 24 * x := by
        have h0 : 0 ≤ Rr := hr0.le.trans hrR
        have h1 : 2 * A * Rr ≤ 2 * (2 * a) * (6 * t₀) :=
          mul_le_mul (by linarith only [hA2]) hRr6 h0 (by positivity)
        rw [hxd]
        linarith only [h1]
      have hNx : 13 * x ≤ (N : ℝ) := by rw [hxd]; linarith only [hNge]
      linarith only [h4A, hNx]
    have hexp2 : 64 * x * Real.exp (-(2 * x)) ≤ 1 := by
      have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * x by positivity)
      have h1 : 64 * x ≤ Real.exp (2 * x) := by nlinarith only [hq, hx32, hx0]
      have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(2 * x))).le
      have h3 : Real.exp (2 * x) * Real.exp (-(2 * x)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      linarith only [h2, h3]
    have hrew : (r / Rr) ^ (2 * N) * (4 * A * Real.exp (2 * A * Rr)) =
        4 * A * ((r / Rr) ^ (2 * N) * Real.exp (2 * A * Rr)) := by ring
    rw [hrew]
    have hsmall : 4 * A * ((r / Rr) ^ (2 * N) * Real.exp (2 * A * Rr)) ≤
        8 * a * Real.exp (-(2 * x)) :=
      mul_le_mul (by linarith only [hA2]) hprod (by positivity) (by positivity)
    have hsmall0 : 0 ≤ 4 * A * ((r / Rr) ^ (2 * N) * Real.exp (2 * A * Rr)) := by positivity
    calc (R.card : ℝ) * (2 * (4 * A * ((r / Rr) ^ (2 * N) * Real.exp (2 * A * Rr))))
        ≤ (t₀ * L) * (2 * (8 * a * Real.exp (-(2 * x)))) :=
          mul_le_mul hRcard (by linarith only [hsmall]) (by positivity) (by positivity)
      _ = L / 4 * (64 * x * Real.exp (-(2 * x))) := by rw [hxd]; ring
      _ ≤ L / 4 * 1 := mul_le_mul_of_nonneg_left hexp2 (by positivity)
      _ = L / 4 := mul_one _
  -- The packet error.
  obtain ⟨ρ, hρd⟩ : ∃ ρ, ρ = τ * ((M : ℝ) + 1) := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := by rw [hρd]; positivity
  have hρE : ρ * E ^ 29 ≤ 1 := by
    have h1 : ρ * E ^ 29 * E ≤ (τ * E ^ 36) * 1 := by
      have h2 : (M : ℝ) + 1 ≤ E ^ 6 := hMle
      have e : ρ * E ^ 29 * E = τ * (((M : ℝ) + 1) * E ^ 30) := by rw [hρd]; ring
      have e' : (τ * E ^ 36) * 1 = τ * (E ^ 6 * E ^ 30) := by ring
      rw [e, e']
      refine mul_le_mul_of_nonneg_left ?_ hτ0.le
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have h3 : ρ * E ^ 29 * E ≤ 2 := by linarith only [h1, hτE]
    have h4 : 0 ≤ ρ * E ^ 29 := by positivity
    nlinarith only [h3, h4, hE]
  have hρ1 : ρ ≤ 1 := by
    have h1 : (1 : ℝ) ≤ E ^ 29 := one_le_pow₀ hE1
    nlinarith only [hρE, h1, hρ0]
  have hρ2E : ρ ^ 2 * E ^ 58 ≤ 1 := by
    have e : ρ ^ 2 * E ^ 58 = (ρ * E ^ 29) ^ 2 := by ring
    rw [e]
    exact pow_le_one₀ (by positivity) hρE
  have hmρ : ((2 * N : ℕ) : ℝ) * ρ ^ 2 * E ^ 38 ≤ 1 := by
    have h2N : ((2 * N : ℕ) : ℝ) ≤ E ^ 20 := by
      push_cast
      have h1 : 2 * (N : ℝ) ≤ E * E ^ 19 := mul_le_mul (by linarith only [hE]) hNle
        (by positivity) hE0.le
      have e : E * E ^ 19 = E ^ 20 := by ring
      linarith only [h1, e]
    have e : ((2 * N : ℕ) : ℝ) * ρ ^ 2 * E ^ 38 ≤ E ^ 20 * ρ ^ 2 * E ^ 38 := by
      gcongr
    have e2 : E ^ 20 * ρ ^ 2 * E ^ 38 = ρ ^ 2 * E ^ 58 := by ring
    linarith only [e, e2, hρ2E]
  have hρ2 : ((2 * N : ℕ) : ℝ) * ρ ^ 2 ≤ 1 / 4 := by
    have h1 : (4 : ℝ) ≤ E ^ 38 := by
      have := hpow (show 1 ≤ 38 by norm_num)
      linarith only [this, hE, pow_one E]
    have h0 : 0 ≤ ((2 * N : ℕ) : ℝ) * ρ ^ 2 := by positivity
    nlinarith only [hmρ, h1, h0]
  have hnear : ∀ k ∈ taperedSupport k₀ M, ∀ y : ℝ, |y| ≤ δ →
      ‖(τ : ℂ) * ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) + I * y - T)‖ ≤ ρ := by
    intro k hk y hy
    rw [mem_taperedSupport_iff] at hk
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ0, hρd]
    refine mul_le_mul_of_nonneg_left ?_ hτ0.le
    have e : (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) + I * y - T =
        (((k - k₀ : ℝ) * (2 * π / L) : ℝ) : ℂ) + I * y := by
      rw [← hx0]
      push_cast
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_pos hgap0]
    have hk' : |(k : ℝ) - k₀| ≤ M := by
      have h : (|k - k₀| : ℤ) ≤ (M : ℤ) := hk.le
      exact_mod_cast h
    have h1 : |(k : ℝ) - k₀| * (2 * π / L) ≤ M * 1 :=
      mul_le_mul hk' hgap (hgap0.le) (Nat.cast_nonneg _)
    linarith only [h1, hy, hδ1]
  have hnearsum : ((taperedSupport k₀ M).card : ℝ) * (2 * (2 * (2 * (((2 * N : ℕ) : ℝ) * ρ ^ 2)) *
      (4 * (a + N * τ) * Real.exp (2 * (a + N * τ) * δ)))) ≤ L / 4 := by
    rw [← hAd]
    have hcard : ((taperedSupport k₀ M).card : ℝ) ≤ E ^ 7 := by
      have h : (taperedSupport k₀ M).card ≤ 2 * M := by
        simp only [taperedSupport]
        rw [Int.card_Ioo]
        omega
      have h1 : ((taperedSupport k₀ M).card : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast h
      have h2 : 2 * ((M : ℝ) + 1) ≤ E * E ^ 6 := mul_le_mul (by linarith only [hE]) hMle
        (by positivity) hE0.le
      have e : E * E ^ 6 = E ^ 7 := by ring
      linarith only [h1, h2, e]
    have hA4' : 4 * A ≤ E ^ 2 := by
      have h1 : 8 * a ≤ E * E := mul_le_mul (by linarith only [hE]) hEa ha0.le hE0.le
      have e : E * E = E ^ 2 := by ring
      linarith only [hA2, h1, e]
    have hexp : Real.exp (2 * A * δ) ≤ E ^ 2 := by
      rw [← hE2]
      refine Real.exp_le_exp.mpr ?_
      nlinarith only [hδ0, hδ1, hA0, hA2]
    have hA40 : 0 ≤ 4 * A := by positivity
    have hprod : 4 * A * Real.exp (2 * A * δ) ≤ E ^ 2 * E ^ 2 :=
      mul_le_mul hA4' hexp (Real.exp_pos _).le (by positivity)
    obtain ⟨w, hwd⟩ : ∃ w, w = ((2 * N : ℕ) : ℝ) * ρ ^ 2 := ⟨_, rfl⟩
    rw [← hwd] at hρ2 hmρ ⊢
    have hw0 : 0 ≤ w := by rw [hwd]; positivity
    have h38 : (0 : ℝ) < E ^ 38 := by positivity
    have hmain : (2 * (2 * (2 * w) * (4 * A * Real.exp (2 * A * δ)))) * E ^ 38 ≤ 8 * E ^ 4 := by
      have h1 : (2 * (2 * (2 * w) * (4 * A * Real.exp (2 * A * δ)))) * E ^ 38 =
          8 * (w * E ^ 38) * (4 * A * Real.exp (2 * A * δ)) := by ring
      rw [h1]
      calc 8 * (w * E ^ 38) * (4 * A * Real.exp (2 * A * δ))
          ≤ 8 * 1 * (E ^ 2 * E ^ 2) :=
            mul_le_mul (by linarith only [hmρ]) hprod (by positivity) (by positivity)
        _ = 8 * E ^ 4 := by ring
    have hfinal : ((taperedSupport k₀ M).card : ℝ) *
        (2 * (2 * (2 * w) * (4 * A * Real.exp (2 * A * δ)))) * E ^ 38 ≤ E ^ 38 := by
      calc ((taperedSupport k₀ M).card : ℝ) *
            (2 * (2 * (2 * w) * (4 * A * Real.exp (2 * A * δ)))) * E ^ 38
          = ((taperedSupport k₀ M).card : ℝ) *
            ((2 * (2 * (2 * w) * (4 * A * Real.exp (2 * A * δ)))) * E ^ 38) := by ring
        _ ≤ E ^ 7 * (8 * E ^ 4) := mul_le_mul hcard hmain (by positivity) (by positivity)
        _ = 8 * E ^ 11 := by ring
        _ ≤ E * E ^ 11 := mul_le_mul_of_nonneg_right (by linarith only [hE]) (by positivity)
        _ = E ^ 12 := by ring
        _ ≤ E ^ 38 := hpow (by norm_num)
    have h1 : ((taperedSupport k₀ M).card : ℝ) *
        (2 * (2 * (2 * w) * (4 * A * Real.exp (2 * A * δ)))) ≤ 1 := by
      refine le_of_mul_le_mul_right ?_ h38
      linarith only [hfinal]
    linarith only [h1, hL16, ha10]
  have hδ' : ∀ k ∈ taperedSupport k₀ M, 0 < biquadraticProfile k₀ M δ k :=
    fun _ hk => biquadraticProfile_pos k₀ hδ0 hk
  have hδ'' : ∀ k ∈ taperedSupport k₀ M, biquadraticProfile k₀ M δ k ≤ 1 / 2 :=
    fun _ hk => (biquadraticProfile_le k₀ M hδ0.le hk).trans hδ1
  have hpos := windowPositiveAt_cutCrystal hL0 k₀ hM2 hδ0 hδ1 ha0.le hτ0.le hτT hA4 R hS hfloor
    hr0 hrR hlow hlowsum hρ1 hρ2 hnear hnearsum
  have hfar : ∀ k : ℤ, k ∉ R → t₀ ≤ |(k : ℝ) * (2 * π / L)| := by
    intro k hk
    have hkabs : (k₁ : ℤ) ≤ |k| := by
      by_contra hn
      apply hk
      rw [not_le] at hn
      have := abs_lt.mp hn
      exact Finset.mem_Ioo.mpr ⟨this.1, this.2⟩
    have hkabs' : (k₁ : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast hkabs
    rw [abs_mul, abs_of_pos hgap0]
    have h1 : t₀ * (L / (2 * π)) * (2 * π / L) ≤ |(k : ℝ)| * (2 * π / L) :=
      mul_le_mul_of_nonneg_right (hk₁ge.trans hkabs') hgap0.le
    have e : t₀ * (L / (2 * π)) * (2 * π / L) = t₀ * ((L / (2 * π)) * (2 * π / L)) := by ring
    rw [e, hdivmul, mul_one] at h1
    exact h1
  have hcount : 6 * (L / (2 * π) + 1) ≤ 2 * Real.log t₀ := by
    rw [ht₀d, Real.log_exp]
    have h1 : 6 * (L / (2 * π)) ≤ L := by
      rw [show 6 * (L / (2 * π)) = 3 * L / π by field_simp; ring, div_le_iff₀ (by positivity)]
      nlinarith only [hL0, hpi3]
    linarith only [h1, hL16, ha10]
  refine ⟨cutClusterConfig hL0 R (taperedSupport k₀ M) (biquadraticProfile k₀ M δ) hδ' hδ'',
    temperedConfig_cutClusterConfig _ _ _ _ _ _,
    cutCluster_local_count hL0 ht₀0 R _ hS _ _ _ hfar hcount,
    ⟨verticalLatticePoint L δ k₀, ?_, by simp [verticalLatticePoint], hx0⟩, ?_, hpos⟩
  · have hk₀S : k₀ ∈ taperedSupport k₀ M := center_mem_taperedSupport k₀ (by omega)
    have hd : biquadraticProfile k₀ M δ k₀ = δ := biquadraticProfile_center k₀ (by omega) δ
    exact Or.inl (Or.inr ⟨⟨k₀, hk₀S⟩, by simp only [hd]⟩)
  · refine ((Set.finite_range fun k : taperedSupport k₀ M =>
        verticalLatticePoint L (biquadraticProfile k₀ M δ k) k).union
      (Set.finite_range fun k : taperedSupport k₀ M =>
        verticalLatticePoint L (-biquadraticProfile k₀ M δ k) k)).subset ?_
    rintro ρ' ⟨((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩), hne⟩
    · exfalso; apply hne; simp [verticalLatticePoint]
    · exact Or.inl ⟨k, rfl⟩
    · exact Or.inr ⟨k, rfl⟩

end GaloisForLFunctions.WindowVisibilityLaw
