import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheMeshPairOfAPacketOpens

/-!
# The compression away from the mesh

The gap law `d(g²)/dt = 8 − 4g²S + O(Kg²)` has its obstruction in the compression `S` of the other zeros. How much of it can occur?

* **An isolated pair opens at the free rate.** If the near zeros are `μ`-separated from each other and from the pair, then `g²S ≤ 4(g/μ)²`, whatever their number. So

  `8 − 16(g/μ)² − 4(2E + K)g² ≤ 2g Re(V′ − V) ≤ 8 + 4Kg²`    (`isolated_pair_rate_ge`, `isolated_pair_rate_le`),

  and a pair much closer than its surroundings has rate `8`, the rate of a double collision.

* **Outside the mesh a pair can close.** The hypothesis on `μ` cannot be dropped: a pair next to a clump of `n ≥ 13` points has negative rate under the Dyson flow (`exists_pair_closes`). So no pointwise bound on `S` holds for a general adjacent pair. The mesh pair (`TheMeshPairOfAPacketOpens`) and the isolated pair are the two cases where a sign is forced.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-! ## The isolated pair -/

/-- **The rate of an isolated pair, from below.** Inside a real simple packet, let the zeros other than `x < x'` within `ρ ≥ 2g` of `x` lie off `[x, x']`, at distance at least `μ` from the pair and from each other, and let the zeros beyond `ρ` have energy at most `E`. No bound on their number enters. -/
theorem isolated_pair_rate_ge {t X K E ρ μ : ℝ} {S : Finset ℂ} {Q : ℂ → ℂ} (ht : 0 < t)
    (hpacket : ∀ a, a ∈ S ↔ riemannHeat t a = 0 ∧ |a.re - X| ≤ 2)
    (hQ : ∀ z, |z.re - X| ≤ 1 → |z.im| ≤ 1 / 2 →
      AnalyticAt ℂ Q z ∧ ‖deriv Q z‖ ≤ K ∧ (riemannHeat t z ≠ 0 →
        logDeriv (riemannHeat t) z = (∑ b ∈ S, (zeroMult (riemannHeat t) b : ℂ) / (z - b)) + Q z))
    {x x' : ℝ} (hxx' : x < x') (hxX : |x - X| < 1) (hx'X : |x' - X| < 1)
    (hx : riemannHeat t (x : ℂ) = 0) (hx' : riemannHeat t (x' : ℂ) = 0)
    (hreal : ∀ b ∈ S, b.im = 0) (hsimple : ∀ b ∈ S, deriv (riemannHeat t) b ≠ 0)
    (hμ : 0 < μ) (hρ : 2 * (x' - x) ≤ ρ)
    (hnear : ∀ b ∈ S, b ≠ (x : ℂ) → b ≠ (x' : ℂ) → |b.re - x| < ρ →
      μ ≤ |b.re - x| ∧ μ ≤ |b.re - x'| ∧ (x' < b.re ∨ b.re < x))
    (hsep : ∀ b ∈ S, ∀ b' ∈ S, b ≠ (x : ℂ) → b ≠ (x' : ℂ) → b' ≠ (x : ℂ) → b' ≠ (x' : ℂ) → b ≠ b' →
      |b.re - x| < ρ → |b'.re - x| < ρ → μ ≤ |b.re - b'.re|)
    (hfar : ∑ b ∈ S.filter (fun b => ρ ≤ |b.re - x|), (zeroMult (riemannHeat t) b : ℝ) / (b.re - x) ^ 2 ≤ E) :
    8 - 16 * ((x' - x) / μ) ^ 2 - 4 * (2 * E + K) * (x' - x) ^ 2 ≤
      2 * (x' - x) * ((zeroVelocity t (x' : ℂ)).re - (zeroVelocity t (x : ℂ)).re) := by
  classical
  have hxre : ((x : ℂ)).re = x := Complex.ofReal_re x
  have hx're : ((x' : ℂ)).re = x' := Complex.ofReal_re x'
  have hne : (x : ℂ) ≠ (x' : ℂ) := fun h => hxx'.ne (Complex.ofReal_injective h)
  have hxS : (x : ℂ) ∈ S := (hpacket _).mpr ⟨hx, by rw [hxre]; linarith only [hxX]⟩
  have hx'S : (x' : ℂ) ∈ S := (hpacket _).mpr ⟨hx', by rw [hx're]; linarith only [hx'X]⟩
  have hK0 : 0 ≤ K := by
    have hin : |((x : ℂ)).re - X| ≤ 1 ∧ |((x : ℂ)).im| ≤ 1 / 2 := by
      constructor
      · rw [hxre]; exact hxX.le
      · rw [Complex.ofReal_im, abs_zero]; norm_num
    exact (norm_nonneg _).trans (hQ _ hin.1 hin.2).2.1
  have hid := gap_rate_eq ht hpacket (fun z h1 h2 => ⟨(hQ z h1 h2).1, (hQ z h1 h2).2.2⟩) hx hx'
    (hsimple _ hxS) (hsimple _ hx'S) hxx' hxX hx'X
  set T := (S.erase (x : ℂ)).erase (x' : ℂ) with hT
  set g := x' - x with hg
  have hgpos : 0 < g := sub_pos.mpr hxx'
  have hρpos : 0 < ρ := by linarith only [hρ, hgpos]
  have hTmem (b : ℂ) (hb : b ∈ T) : b ∈ S ∧ b ≠ (x : ℂ) ∧ b ≠ (x' : ℂ) := by
    obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hb
    obtain ⟨h3, h4⟩ := Finset.mem_erase.mp h2
    exact ⟨h4, h3, h1⟩
  have hbof (b : ℂ) (hb : b ∈ S) : b = ((b.re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [hreal b hb])
  -- the near zeros other than the pair
  set N := T.filter (fun b => |b.re - x| < ρ) with hN
  set F := T.filter (fun b => ρ ≤ |b.re - x|) with hF
  have hNmem (b : ℂ) (hb : b ∈ N) : b ∈ T ∧ |b.re - x| < ρ := Finset.mem_filter.mp hb
  have hinj : Set.InjOn Complex.re (T : Set ℂ) := by
    intro a ha b hb hab
    rw [hbof a (hTmem a ha).1, hbof b (hTmem b hb).1, hab]
  have hdist (b : ℂ) (hb : b ∈ N) : μ ≤ |b.re - x| ∧ μ ≤ |b.re - x'| ∧ (x' < b.re ∨ b.re < x) := by
    obtain ⟨hbT, hbn⟩ := hNmem b hb
    obtain ⟨h1, h2, h3⟩ := hTmem b hbT
    exact hnear b h1 h2 h3 hbn
  have hside (b : ℂ) (hb : b ∈ N) : x' < b.re ∨ b.re < x := (hdist b hb).2.2
  set R := (N.filter fun b => x' < b.re).image Complex.re with hR
  set Le := (N.filter fun b => b.re < x).image Complex.re with hLe
  have hNinj : Set.InjOn Complex.re (N : Set ℂ) := hinj.mono fun a ha => (hNmem a ha).1
  have hsepre (a b : ℂ) (ha : a ∈ N) (hb : b ∈ N) (h : a.re ≠ b.re) : μ ≤ |a.re - b.re| := by
    obtain ⟨h1, h2, h3⟩ := hTmem a (hNmem a ha).1
    obtain ⟨h4, h5, h6⟩ := hTmem b (hNmem b hb).1
    exact hsep a h1 b h4 h2 h3 h5 h6 (fun heq => h (by rw [heq])) (hNmem a ha).2 (hNmem b hb).2
  have hcomp := sum_inv_mul_le_of_mesh (x := x) (x' := x') hμ hxx'.le (R := R) (Le := Le)
    (by
      intro a ha a' ha' hne'
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp ha'
      exact hsepre b b' (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hb').1 hne')
    (by
      intro a ha a' ha' hne'
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp ha'
      exact hsepre b b' (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hb').1 hne')
    (by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hb
      have := (hdist b h1).2.1
      rwa [abs_of_pos (by linarith only [h2])] at this)
    (by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hb
      have := (hdist b h1).1
      rwa [abs_of_neg (by linarith only [h2]), neg_sub] at this)
  -- each term of the compression
  have hterm (b : ℂ) (hb : b ∈ T) :
      ((zeroMult (riemannHeat t) b : ℂ) / (((x' : ℂ) - b) * ((x : ℂ) - b))).re =
        1 / ((x' - b.re) * (x - b.re)) := by
    have hm := zeroMult_riemannHeat_eq_one ht.le ((hpacket b).mp (hTmem b hb).1).1
      (hsimple b (hTmem b hb).1)
    rw [hm, Nat.cast_one]
    have hb' := hbof b (hTmem b hb).1
    rw [hb', ← Complex.ofReal_sub, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
      show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_div, Complex.ofReal_re]
    simp
  have hsplitT : Disjoint N F := Finset.disjoint_left.mpr fun b h1 h2 =>
    absurd (Finset.mem_filter.mp h2).2 (not_le.mpr (Finset.mem_filter.mp h1).2)
  have hunionT : T = N ∪ F := by
    ext b
    simp only [hN, hF, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hb
      rcases lt_or_ge |b.re - x| ρ with h | h
      · exact Or.inl ⟨hb, h⟩
      · exact Or.inr ⟨hb, h⟩
    · rintro (h | h) <;> exact h.1
  have hrecomp : (pairCompression t T x x').re =
      (∑ w ∈ R, 1 / ((x' - w) * (x - w)) + ∑ w ∈ Le, 1 / ((x' - w) * (x - w))) +
        ∑ b ∈ F, 1 / ((x' - b.re) * (x - b.re)) := by
    rw [pairCompression, Complex.re_sum, Finset.sum_congr rfl hterm]
    have hsplit : N = (N.filter fun b => x' < b.re) ∪ (N.filter fun b => b.re < x) := by
      ext b
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hb
        rcases hside b hb with h | h
        · exact Or.inl ⟨hb, h⟩
        · exact Or.inr ⟨hb, h⟩
      · rintro (h | h) <;> exact h.1
    have hdisj : Disjoint (N.filter fun b => x' < b.re) (N.filter fun b => b.re < x) :=
      Finset.disjoint_left.mpr fun b h1 h2 => by
        have h3 := (Finset.mem_filter.mp h1).2
        have h4 := (Finset.mem_filter.mp h2).2
        linarith only [h3, h4, hxx']
    conv_lhs => rw [hunionT, Finset.sum_union hsplitT, hsplit, Finset.sum_union hdisj]
    rw [hR, hLe, Finset.sum_image (hNinj.mono fun a ha => (Finset.mem_filter.mp ha).1),
      Finset.sum_image (hNinj.mono fun a ha => (Finset.mem_filter.mp ha).1)]
  -- the far zeros
  have hFsub : F ⊆ S.filter (fun b => ρ ≤ |b.re - x|) := by
    intro b hb
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨(hTmem b h1).1, h2⟩
  have hfarsum : ∑ b ∈ F, 1 / ((x' - b.re) * (x - b.re)) ≤ 2 * E := by
    have h1 : ∑ b ∈ F, 1 / ((x' - b.re) * (x - b.re)) ≤
        ∑ b ∈ F, 2 * ((zeroMult (riemannHeat t) b : ℝ) / (b.re - x) ^ 2) := by
      refine Finset.sum_le_sum fun b hb => ?_
      obtain ⟨hbT, hbρ⟩ := Finset.mem_filter.mp hb
      have hm := zeroMult_riemannHeat_eq_one ht.le ((hpacket b).mp (hTmem b hbT).1).1
        (hsimple b (hTmem b hbT).1)
      rw [hm, Nat.cast_one]
      set d := |b.re - x| with hd
      have hdpos : 0 < d := hρpos.trans_le hbρ
      have hsq : (b.re - x) ^ 2 = d ^ 2 := by rw [hd, sq_abs]
      rw [hsq]
      have hgd : g ≤ d / 2 := by linarith only [hρ, hbρ]
      have hprod : d ^ 2 / 2 ≤ (x' - b.re) * (x - b.re) := by
        rcases le_or_gt 0 (b.re - x) with h | h
        · have hd2 : d = b.re - x := by rw [hd, abs_of_nonneg h]
          have h1 : (x' - b.re) * (x - b.re) = (d - g) * d := by
            rw [hd2, hg]
            ring
          rw [h1]
          nlinarith only [hgd, hdpos]
        · have hd2 : d = x - b.re := by rw [hd, abs_of_neg h]; ring
          have h1 : (x' - b.re) * (x - b.re) = (d + g) * d := by
            rw [hd2, hg]
            ring
          rw [h1]
          nlinarith only [hgpos, hdpos]
      have hd2 : 0 < d ^ 2 / 2 := by positivity
      calc 1 / ((x' - b.re) * (x - b.re)) ≤ 1 / (d ^ 2 / 2) := one_div_le_one_div_of_le hd2 hprod
        _ = 2 * (1 / d ^ 2) := by field_simp
    refine h1.trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (le_trans ?_ hfar) (by norm_num)
    exact Finset.sum_le_sum_of_subset_of_nonneg hFsub fun _ _ _ => by positivity
  -- the exterior increment
  have hincr : ‖Q (x' : ℂ) - Q (x : ℂ)‖ ≤ K * g := by
    set D : Set ℂ := {z | |z.re - X| ≤ 1 ∧ |z.im| ≤ 1 / 2} with hDdef
    have hDc : Convex ℝ D := by
      have h1 : Convex ℝ {z : ℂ | |z.re - X| ≤ 1} := by
        have : {z : ℂ | |z.re - X| ≤ 1} = Complex.re ⁻¹' (Set.Icc (X - 1) (X + 1)) := by
          ext z
          simp only [mem_setOf_eq, mem_preimage, mem_Icc, abs_le]
          constructor
          · rintro ⟨h1, h2⟩; constructor <;> linarith only [h1, h2]
          · rintro ⟨h1, h2⟩; constructor <;> linarith only [h1, h2]
        rw [this]
        exact (convex_Icc _ _).is_linear_preimage Complex.reLm.isLinear
      have h2 : Convex ℝ {z : ℂ | |z.im| ≤ 1 / 2} := by
        have : {z : ℂ | |z.im| ≤ 1 / 2} = Complex.im ⁻¹' (Set.Icc (-(1 / 2)) (1 / 2)) := by
          ext z
          simp only [mem_setOf_eq, mem_preimage, mem_Icc, abs_le]
        rw [this]
        exact (convex_Icc _ _).is_linear_preimage Complex.imLm.isLinear
      exact h1.inter h2
    have hinD (y : ℝ) (hy : |y - X| < 1) : (y : ℂ) ∈ D := by
      constructor
      · rw [Complex.ofReal_re]; exact hy.le
      · rw [Complex.ofReal_im, abs_zero]; norm_num
    have h := hDc.norm_image_sub_le_of_norm_deriv_le (f := Q) (C := K)
      (fun z hz => (hQ z hz.1 hz.2).1.differentiableAt) (fun z hz => (hQ z hz.1 hz.2).2.1)
      (hinD x hxX) (hinD x' hx'X)
    have hnorm : ‖(x' : ℂ) - x‖ = g := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hgpos]
    rwa [hnorm] at h
  -- the real part of the identity
  have hre := congrArg Complex.re hid
  have hgc : ((g : ℝ) : ℂ) ^ 2 = ((g ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hgc] at hre
  have hmul : (((g : ℝ) : ℂ) * (zeroVelocity t (x' : ℂ) - zeroVelocity t (x : ℂ))).re =
      g * ((zeroVelocity t (x' : ℂ)).re - (zeroVelocity t (x : ℂ)).re) := by
    rw [Complex.re_ofReal_mul, Complex.sub_re]
  have hmul2 : (2 * ((g ^ 2 : ℝ) : ℂ) * pairCompression t T x x').re =
      2 * g ^ 2 * (pairCompression t T x x').re := by
    rw [show (2 : ℂ) * ((g ^ 2 : ℝ) : ℂ) = ((2 * g ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
  have hmul3 : (2 * ((g : ℝ) : ℂ) * (Q (x' : ℂ) - Q (x : ℂ))).re =
      2 * g * (Q (x' : ℂ) - Q (x : ℂ)).re := by
    rw [show (2 : ℂ) * ((g : ℝ) : ℂ) = ((2 * g : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
  simp only [Complex.add_re, Complex.sub_re] at hre
  rw [hmul, hmul2, hmul3] at hre
  have h4 : ((4 : ℂ)).re = 4 := by norm_num
  rw [h4] at hre
  have hQre : -(K * g) ≤ (Q (x' : ℂ) - Q (x : ℂ)).re := by
    have h1 := Complex.abs_re_le_norm (Q (x' : ℂ) - Q (x : ℂ))
    have h2 := (abs_le.mp (h1.trans hincr)).1
    linarith only [h2]
  have hg2 : 0 < g ^ 2 := by positivity
  have hbound : g ^ 2 * (pairCompression t T x x').re ≤ 4 * (g / μ) ^ 2 + 2 * E * g ^ 2 := by
    rw [hrecomp, mul_add]
    have h1 := mul_le_mul_of_nonneg_left hcomp hg2.le
    have h3 : g ^ 2 * (4 / μ ^ 2) = 4 * (g / μ) ^ 2 := by
      field_simp
    rw [h3] at h1
    have h2 := mul_le_mul_of_nonneg_left hfarsum hg2.le
    linarith only [h1, h2]
  have h6 : 2 * g * -(K * g) ≤ 2 * g * (Q (x' : ℂ) - Q (x : ℂ)).re :=
    mul_le_mul_of_nonneg_left hQre (by positivity)
  nlinarith only [hre, hbound, h6]

/-- **The rate of an isolated pair, from above.** The same pair opens at rate at most `8 + 4Kg²`. -/
theorem isolated_pair_rate_le {t X K ρ : ℝ} {S : Finset ℂ} {Q : ℂ → ℂ} (ht : 0 < t)
    (hpacket : ∀ a, a ∈ S ↔ riemannHeat t a = 0 ∧ |a.re - X| ≤ 2)
    (hQ : ∀ z, |z.re - X| ≤ 1 → |z.im| ≤ 1 / 2 →
      AnalyticAt ℂ Q z ∧ ‖deriv Q z‖ ≤ K ∧ (riemannHeat t z ≠ 0 →
        logDeriv (riemannHeat t) z = (∑ b ∈ S, (zeroMult (riemannHeat t) b : ℂ) / (z - b)) + Q z))
    {x x' : ℝ} (hxx' : x < x') (hxX : |x - X| < 1) (hx'X : |x' - X| < 1)
    (hx : riemannHeat t (x : ℂ) = 0) (hx' : riemannHeat t (x' : ℂ) = 0)
    (hreal : ∀ b ∈ S, b.im = 0) (hsimple : ∀ b ∈ S, deriv (riemannHeat t) b ≠ 0)
    (hρ : 2 * (x' - x) ≤ ρ)
    (hnear : ∀ b ∈ S, b ≠ (x : ℂ) → b ≠ (x' : ℂ) → |b.re - x| < ρ → x' < b.re ∨ b.re < x) :
    2 * (x' - x) * ((zeroVelocity t (x' : ℂ)).re - (zeroVelocity t (x : ℂ)).re) ≤
      8 + 4 * K * (x' - x) ^ 2 := by
  have hxre : ((x : ℂ)).re = x := Complex.ofReal_re x
  have hx're : ((x' : ℂ)).re = x' := Complex.ofReal_re x'
  have hxS : (x : ℂ) ∈ S := (hpacket _).mpr ⟨hx, by rw [hxre]; linarith only [hxX]⟩
  have hx'S : (x' : ℂ) ∈ S := (hpacket _).mpr ⟨hx', by rw [hx're]; linarith only [hx'X]⟩
  refine gap_rate_le ht hpacket hQ hx hx' (hsimple _ hxS) (hsimple _ hx'S) hxx' hxX hx'X ?_
  intro b hb0 hb2 hbx hbx'
  have hbS : b ∈ S := (hpacket b).mpr ⟨hb0, hb2⟩
  rw [hreal b hbS]
  have hout : x' < b.re ∨ b.re < x := by
    rcases lt_or_ge |b.re - x| ρ with h | h
    · exact hnear b hbS hbx hbx' h
    · rcases le_or_gt x b.re with h1 | h1
      · left
        rw [abs_of_nonneg (by linarith only [h1])] at h
        linarith only [h, hρ, hxx']
      · exact Or.inr h1
  have hg : 0 < x' - x := sub_pos.mpr hxx'
  rcases hout with h | h
  · nlinarith only [h, hg]
  · nlinarith only [h, hg]

/-! ## A pair can close outside the mesh -/

/-- A pair `0, 1` next to a clump of `n` points in `[2, 3)`. -/
def clumpPoint (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | (k + 2) => 2 + (k : ℝ) / n

theorem clumpPoint_strictMono {n : ℕ} (hn : 0 < n) : StrictMono (clumpPoint n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine strictMono_nat_of_lt_succ fun k => ?_
  match k with
  | 0 => simp [clumpPoint]
  | 1 =>
    simp only [clumpPoint, Nat.cast_zero, zero_div]
    norm_num
  | (k + 2) =>
    simp only [clumpPoint]
    push_cast
    have : (k : ℝ) / n < ((k : ℝ) + 1) / n := div_lt_div_of_pos_right (by linarith only) hn'
    linarith only [this]

/-- **Outside the mesh a pair can close.** With a clump of `n ≥ 13` points next to it, the pair `0, 1` has negative rate under the Dyson flow. -/
theorem exists_pair_closes {n : ℕ} (hn : 13 ≤ n) :
    ∃ y : Fin (n + 2) → ℝ, StrictMono y ∧ ∃ i j : Fin (n + 2), i < j ∧
      2 * (y j - y i) * (dysonVelocity y j - dysonVelocity y i) < 0 := by
  classical
  have hn0 : 0 < n := by omega
  have hnr : (13 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith only [hnr]
  set y : Fin (n + 2) → ℝ := fun k => clumpPoint n k with hy
  have hstrict : StrictMono y := fun a b h => clumpPoint_strictMono hn0 (Fin.lt_def.mp h)
  set i : Fin (n + 2) := ⟨0, by omega⟩ with hi
  set j : Fin (n + 2) := ⟨1, by omega⟩ with hj
  have hij : i < j := by
    rw [Fin.lt_def]
    simp [hi, hj]
  refine ⟨y, hstrict, i, j, hij, ?_⟩
  rw [rate_eq_of_dyson hij.ne hstrict.injective]
  have hyi : y i = 0 := rfl
  have hyj : y j = 1 := rfl
  rw [hyi, hyj]
  set T := (Finset.univ.erase i).erase j with hT
  have hcard : T.card = n := by
    have h1 : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.ne', Finset.mem_univ _⟩
    rw [hT, Finset.card_erase_of_mem h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
    omega
  have hterm (k : Fin (n + 2)) (hk : k ∈ T) : (1 : ℝ) / 6 ≤ 1 / ((1 - y k) * (0 - y k)) := by
    obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hk
    obtain ⟨h3, -⟩ := Finset.mem_erase.mp h2
    have hk0 : k.val ≠ 0 := fun h => h3 (Fin.ext h)
    have hk1 : k.val ≠ 1 := fun h => h1 (Fin.ext h)
    obtain ⟨m, hm⟩ : ∃ m, k.val = m + 2 := ⟨k.val - 2, by omega⟩
    have hmn : m < n := by
      have := k.isLt
      omega
    have hval : y k = 2 + (m : ℝ) / n := by
      change clumpPoint n k.val = _
      rw [hm]
      rfl
    have hm0 : (0 : ℝ) ≤ (m : ℝ) / n := by positivity
    have hm1 : (m : ℝ) / n ≤ 1 := by
      rw [div_le_one hnpos]
      exact_mod_cast hmn.le
    rw [hval]
    set q := (m : ℝ) / n with hq
    have heq : (1 - (2 + q)) * (0 - (2 + q)) = (1 + q) * (2 + q) := by ring
    rw [heq]
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith only [hm0, hm1]
  have hsum : (n : ℝ) * (1 / 6) ≤ ∑ k ∈ T, 1 / ((1 - y k) * (0 - y k)) := by
    have h := Finset.card_nsmul_le_sum T _ _ hterm
    rwa [hcard, nsmul_eq_mul] at h
  have h1 : (1 - (0 : ℝ)) ^ 2 = 1 := by norm_num
  rw [h1]
  linarith only [hsum, hnr]

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
