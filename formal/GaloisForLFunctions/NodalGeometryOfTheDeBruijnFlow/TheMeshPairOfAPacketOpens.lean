import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheGapLawOfAdjacentZeros
import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheDysonFlowKeepsTheMesh

/-!
# The mesh pair of a packet opens

Control of the compression on a cluster. Let all zeros of `H_t` in the packet at height `X` be real and simple. If a pair `x < x'` in the
inner window has the least gap `g` of the packet, the compression of the others is below that of a lattice, so

`2g Re(V(x') − V(x)) ≥ 16/n − 4K g²`    (`mesh_pair_rate_ge`),

with `n` the size of the packet and `K ≪ log X` the Lipschitz constant of the exterior field. Since `n ≪ log X`, a mesh pair below the scale
`c/log X` opens at rate `≫ 1/log X` (`exists_mesh_pair_opens`). The factor `1/n` is the price of a cluster: at a zero of order `m` the
gaps open at rate `≍ 1/m`.

Only the zeros near the pair need to be counted. If `n` zeros of the packet lie within `ρ` of `x`, at least `g`-separated, and the others have energy `E = Σ_b m_b/|b − x|²` at `x`, then
`2g Re(V(x') − V(x)) ≥ 16/n − 4(2E + K) g²` (`local_pair_rate_ge`). At normal density `E ≍ log²X/n`, so the rate is `≍ 1/n` up to `g² ≍ log⁻²X`.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-- **The rate at the mesh pair of a real packet.** -/
theorem mesh_pair_rate_ge {t X K : ℝ} {S : Finset ℂ} {Q : ℂ → ℂ} (ht : 0 < t)
    (hpacket : ∀ a, a ∈ S ↔ riemannHeat t a = 0 ∧ |a.re - X| ≤ 2)
    (hQ : ∀ z, |z.re - X| ≤ 1 → |z.im| ≤ 1 / 2 →
      AnalyticAt ℂ Q z ∧ ‖deriv Q z‖ ≤ K ∧ (riemannHeat t z ≠ 0 →
        logDeriv (riemannHeat t) z = (∑ b ∈ S, (zeroMult (riemannHeat t) b : ℂ) / (z - b)) + Q z))
    {x x' : ℝ} (hxx' : x < x') (hxX : |x - X| < 1) (hx'X : |x' - X| < 1)
    (hx : riemannHeat t (x : ℂ) = 0) (hx' : riemannHeat t (x' : ℂ) = 0)
    (hreal : ∀ b ∈ S, b.im = 0) (hsimple : ∀ b ∈ S, deriv (riemannHeat t) b ≠ 0)
    (hsep : ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → x' - x ≤ |b.re - b'.re|) :
    16 / (S.card : ℝ) - 4 * K * (x' - x) ^ 2 ≤
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
  -- real positions of the rest of the packet
  have hTmem (b : ℂ) (hb : b ∈ T) : b ∈ S ∧ b ≠ (x : ℂ) ∧ b ≠ (x' : ℂ) := by
    obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hb
    obtain ⟨h3, h4⟩ := Finset.mem_erase.mp h2
    exact ⟨h4, h3, h1⟩
  have hbof (b : ℂ) (hb : b ∈ S) : b = ((b.re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [hreal b hb])
  set R := (T.filter fun b => x' < b.re).image Complex.re with hR
  set Le := (T.filter fun b => b.re < x).image Complex.re with hLe
  have hinj : Set.InjOn Complex.re (T : Set ℂ) := by
    intro a ha b hb hab
    rw [hbof a (hTmem a ha).1, hbof b (hTmem b hb).1, hab]
  have hsepre (a b : ℂ) (ha : a ∈ T) (hb : b ∈ T) (h : a.re ≠ b.re) : g ≤ |a.re - b.re| :=
    hsep a (hTmem a ha).1 b (hTmem b hb).1 fun heq => h (by rw [heq])
  have hdist (b : ℂ) (hb : b ∈ T) : g ≤ |b.re - x| ∧ g ≤ |b.re - x'| := by
    obtain ⟨h1, h2, h3⟩ := hTmem b hb
    have h4 := hsep b h1 _ hxS h2
    have h5 := hsep b h1 _ hx'S h3
    rw [hxre] at h4
    rw [hx're] at h5
    exact ⟨h4, h5⟩
  have hside (b : ℂ) (hb : b ∈ T) : x' < b.re ∨ b.re < x := by
    obtain ⟨h1, h2⟩ := hdist b hb
    by_contra hcon
    push Not at hcon
    obtain ⟨h3, h4⟩ := hcon
    rw [abs_of_nonneg (by linarith only [h4])] at h1
    have h5 : b.re = x' := by
      have : x' ≤ b.re := by
        rw [hg] at h1
        linarith only [h1]
      linarith only [this, h3]
    apply (hTmem b hb).2.2
    rw [hbof b (hTmem b hb).1, h5]
  have hcomp := sum_inv_mul_le_of_sep (x := x) (x' := x') hgpos rfl (R := R) (Le := Le)
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
      have := (hdist b h1).2
      rwa [abs_of_pos (by linarith only [h2])] at this)
    (by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hb
      have := (hdist b h1).1
      rwa [abs_of_neg (by linarith only [h2]), neg_sub] at this)
  have hRcard : R.card = (T.filter fun b => x' < b.re).card :=
    Finset.card_image_of_injOn (hinj.mono fun a ha => (Finset.mem_filter.mp ha).1)
  have hLcard : Le.card = (T.filter fun b => b.re < x).card :=
    Finset.card_image_of_injOn (hinj.mono fun a ha => (Finset.mem_filter.mp ha).1)
  -- the compression as a real sum
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
  have hrecomp : (pairCompression t T x x').re =
      ∑ w ∈ R, 1 / ((x' - w) * (x - w)) + ∑ w ∈ Le, 1 / ((x' - w) * (x - w)) := by
    rw [pairCompression, Complex.re_sum, Finset.sum_congr rfl hterm]
    have hsplit : T = (T.filter fun b => x' < b.re) ∪ (T.filter fun b => b.re < x) := by
      ext b
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hb
        rcases hside b hb with h | h
        · exact Or.inl ⟨hb, h⟩
        · exact Or.inr ⟨hb, h⟩
      · rintro (h | h) <;> exact h.1
    have hdisj : Disjoint (T.filter fun b => x' < b.re) (T.filter fun b => b.re < x) :=
      Finset.disjoint_left.mpr fun b h1 h2 => by
        have h3 := (Finset.mem_filter.mp h1).2
        have h4 := (Finset.mem_filter.mp h2).2
        linarith only [h3, h4, hxx']
    conv_lhs => rw [hsplit, Finset.sum_union hdisj]
    rw [hR, hLe, Finset.sum_image (hinj.mono fun a ha => (Finset.mem_filter.mp ha).1),
      Finset.sum_image (hinj.mono fun a ha => (Finset.mem_filter.mp ha).1)]
  have hcard : (R.card : ℝ) + (Le.card : ℝ) + 2 = (S.card : ℝ) := by
    have hTcard : T.card + 2 = S.card := by
      have h1 : (S.erase (x : ℂ)).card + 1 = S.card := Finset.card_erase_add_one hxS
      have h2 : T.card + 1 = (S.erase (x : ℂ)).card :=
        Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hne.symm, hx'S⟩)
      omega
    have hsumcard : (T.filter fun b => x' < b.re).card + (T.filter fun b => b.re < x).card = T.card := by
      have hsplit : (T.filter fun b => x' < b.re) ∪ (T.filter fun b => b.re < x) = T := by
        ext b
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (h | h) <;> exact h.1
        · intro hb
          rcases hside b hb with h | h
          · exact Or.inl ⟨hb, h⟩
          · exact Or.inr ⟨hb, h⟩
      have hdisj : Disjoint (T.filter fun b => x' < b.re) (T.filter fun b => b.re < x) :=
        Finset.disjoint_left.mpr fun b h1 h2 => by
          have h3 := (Finset.mem_filter.mp h1).2
          have h4 := (Finset.mem_filter.mp h2).2
          linarith only [h3, h4, hxx']
      rw [← Finset.card_union_of_disjoint hdisj, hsplit]
    rw [hRcard, hLcard]
    have : (T.filter fun b => x' < b.re).card + (T.filter fun b => b.re < x).card + 2 = S.card := by
      omega
    exact_mod_cast this
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
  have hbound : g ^ 2 * (pairCompression t T x x').re ≤
      2 - 1 / ((R.card : ℝ) + 1) - 1 / ((Le.card : ℝ) + 1) := by
    rw [hrecomp]
    have := mul_le_mul_of_nonneg_left hcomp hg2.le
    rwa [mul_div_cancel₀ _ hg2.ne'] at this
  have hRn : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  have hLn : (0 : ℝ) ≤ Le.card := Nat.cast_nonneg _
  have h16 := sixteen_div_le _ _ hRn hLn
  rw [hcard] at h16
  have hr1 : 4 / ((R.card : ℝ) + 1) = 4 * (1 / ((R.card : ℝ) + 1)) := by ring
  have hr2 : 4 / ((Le.card : ℝ) + 1) = 4 * (1 / ((Le.card : ℝ) + 1)) := by ring
  have h6 : 2 * g * -(K * g) ≤ 2 * g * (Q (x' : ℂ) - Q (x : ℂ)).re :=
    mul_le_mul_of_nonneg_left hQre (by positivity)
  nlinarith only [hre, hbound, h16, h6, hr1, hr2]

/-- **A mesh pair below the spacing opens.** Inside a real simple packet, a mesh pair with `g ≤ c/log X` has
`d(g²)/dt ≥ c'/log X`. -/
theorem exists_mesh_pair_opens :
    ∃ C > 0, ∃ X₀ : ℝ, 4096 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ t : ℝ, 0 < t → t ≤ 1 / 8 → t * Real.log X ≤ 1 →
      ∀ x x' : ℝ, x < x' → |x - X| < 1 → |x' - X| < 1 →
      riemannHeat t (x : ℂ) = 0 → riemannHeat t (x' : ℂ) = 0 →
      (∀ b, riemannHeat t b = 0 → |b.re - X| ≤ 2 → b.im = 0 ∧ deriv (riemannHeat t) b ≠ 0 ∧
        ∀ b', riemannHeat t b' = 0 → |b'.re - X| ≤ 2 → b ≠ b' → x' - x ≤ |b.re - b'.re|) →
      (x' - x) ^ 2 ≤ 1 / (C * Real.log X) ^ 2 →
      1 / (C * Real.log X) ≤
        2 * (x' - x) * ((zeroVelocity t (x' : ℂ)).re - (zeroVelocity t (x : ℂ)).re) := by
  obtain ⟨C₀, hC₀, X₀, hX₀, hforce⟩ := exists_uniform_riemannHeat_exterior_force
  refine ⟨4 * C₀, by positivity, X₀, hX₀, ?_⟩
  intro X hX t ht ht8 htX x x' hxx' hxX hx'X hx hx' hall hsmall
  have hL : 0 < Real.log X := Real.log_pos (by linarith only [hX, hX₀])
  obtain ⟨S, Q, hpacket, hcount, -, hQ⟩ := hforce X hX t ht.le ht8 htX
  set K := C₀ * Real.log X with hK
  have hKpos : 0 < K := by positivity
  have hsimple : ∀ b ∈ S, deriv (riemannHeat t) b ≠ 0 := fun b hb =>
    (hall b ((hpacket b).mp hb).1 ((hpacket b).mp hb).2).2.1
  have hrate := mesh_pair_rate_ge (K := K) ht hpacket
    (fun z h1 h2 => ⟨(hQ z h1 h2).1, (hQ z h1 h2).2.2.1, (hQ z h1 h2).2.2.2.2⟩) hxx' hxX hx'X hx hx'
    (fun b hb => (hall b ((hpacket b).mp hb).1 ((hpacket b).mp hb).2).1) hsimple
    (fun b hb b' hb' hne => (hall b ((hpacket b).mp hb).1 ((hpacket b).mp hb).2).2.2 b'
      ((hpacket b').mp hb').1 ((hpacket b').mp hb').2 hne)
  -- the packet size is at most `K`
  have hcard : (S.card : ℝ) ≤ K := by
    refine le_trans ?_ hcount
    have : S.card ≤ ∑ a ∈ S, zeroMult (riemannHeat t) a := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun a ha =>
        one_le_zeroMult_riemannHeat ht.le ((hpacket a).mp ha).1
    exact_mod_cast this
  have hSpos : (0 : ℝ) < S.card := by
    have hxS : (x : ℂ) ∈ S := (hpacket _).mpr ⟨hx, by rw [Complex.ofReal_re]; linarith only [hxX]⟩
    exact_mod_cast Finset.card_pos.mpr ⟨_, hxS⟩
  have h16 : 16 / K ≤ 16 / (S.card : ℝ) := div_le_div_of_nonneg_left (by norm_num) hSpos hcard
  have hsmall' : (x' - x) ^ 2 ≤ 1 / (16 * K ^ 2) := by
    refine hsmall.trans (le_of_eq ?_)
    rw [hK]
    ring
  have hquad : 4 * K * (x' - x) ^ 2 ≤ 1 / (4 * K) := by
    have := mul_le_mul_of_nonneg_left hsmall' (by positivity : 0 ≤ 4 * K)
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  have hgoal : 1 / (4 * C₀ * Real.log X) = 1 / (4 * K) := by
    rw [hK]
    ring_nf
  rw [hgoal]
  have hsplit : 16 / K = 64 * (1 / (4 * K)) := by
    field_simp
    ring
  have hpos : 0 < 1 / (4 * K) := by positivity
  linarith only [hrate, h16, hquad, hsplit, hpos]

/-- **The rate with a local count.** Inside a real simple packet, let the `n` zeros within `ρ ≥ 2g` of `x` be at least `g`-separated, and let the other zeros have energy at most `E` at `x`. Then the squared gap of the pair opens at rate at least `16/n − 4(2E + K) g²`. -/
theorem local_pair_rate_ge {t X K E ρ : ℝ} {n : ℕ} {S : Finset ℂ} {Q : ℂ → ℂ} (ht : 0 < t)
    (hpacket : ∀ a, a ∈ S ↔ riemannHeat t a = 0 ∧ |a.re - X| ≤ 2)
    (hQ : ∀ z, |z.re - X| ≤ 1 → |z.im| ≤ 1 / 2 →
      AnalyticAt ℂ Q z ∧ ‖deriv Q z‖ ≤ K ∧ (riemannHeat t z ≠ 0 →
        logDeriv (riemannHeat t) z = (∑ b ∈ S, (zeroMult (riemannHeat t) b : ℂ) / (z - b)) + Q z))
    {x x' : ℝ} (hxx' : x < x') (hxX : |x - X| < 1) (hx'X : |x' - X| < 1)
    (hx : riemannHeat t (x : ℂ) = 0) (hx' : riemannHeat t (x' : ℂ) = 0)
    (hreal : ∀ b ∈ S, b.im = 0) (hsimple : ∀ b ∈ S, deriv (riemannHeat t) b ≠ 0)
    (hρ : 2 * (x' - x) ≤ ρ)
    (hsep : ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → |b.re - x| < ρ → |b'.re - x| < ρ → x' - x ≤ |b.re - b'.re|)
    (hcount : ((S.filter fun b => |b.re - x| < ρ).card : ℝ) ≤ n)
    (hfar : ∑ b ∈ S.filter (fun b => ρ ≤ |b.re - x|), (zeroMult (riemannHeat t) b : ℝ) / (b.re - x) ^ 2 ≤ E) :
    16 / (n : ℝ) - 4 * (2 * E + K) * (x' - x) ^ 2 ≤
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
  have hxnear : |((x : ℂ)).re - x| < ρ := by
    rw [hxre, sub_self, abs_zero]
    exact hρpos
  have hx'near : |((x' : ℂ)).re - x| < ρ := by
    rw [hx're, abs_of_pos hgpos]
    linarith only [hρ, hgpos]
  -- the near zeros other than the pair
  set N := T.filter (fun b => |b.re - x| < ρ) with hN
  set F := T.filter (fun b => ρ ≤ |b.re - x|) with hF
  have hNmem (b : ℂ) (hb : b ∈ N) : b ∈ T ∧ |b.re - x| < ρ := Finset.mem_filter.mp hb
  have hinj : Set.InjOn Complex.re (T : Set ℂ) := by
    intro a ha b hb hab
    rw [hbof a (hTmem a ha).1, hbof b (hTmem b hb).1, hab]
  have hdist (b : ℂ) (hb : b ∈ N) : g ≤ |b.re - x| ∧ g ≤ |b.re - x'| := by
    obtain ⟨hbT, hbn⟩ := hNmem b hb
    obtain ⟨h1, h2, h3⟩ := hTmem b hbT
    have h4 := hsep b h1 _ hxS h2 hbn hxnear
    have h5 := hsep b h1 _ hx'S h3 hbn hx'near
    rw [hxre] at h4
    rw [hx're] at h5
    exact ⟨h4, h5⟩
  have hside (b : ℂ) (hb : b ∈ N) : x' < b.re ∨ b.re < x := by
    obtain ⟨h1, h2⟩ := hdist b hb
    by_contra hcon
    push Not at hcon
    obtain ⟨h3, h4⟩ := hcon
    rw [abs_of_nonneg (by linarith only [h4])] at h1
    have h5 : b.re = x' := by
      have : x' ≤ b.re := by
        rw [hg] at h1
        linarith only [h1]
      linarith only [this, h3]
    apply (hTmem b (hNmem b hb).1).2.2
    rw [hbof b (hTmem b (hNmem b hb).1).1, h5]
  set R := (N.filter fun b => x' < b.re).image Complex.re with hR
  set Le := (N.filter fun b => b.re < x).image Complex.re with hLe
  have hNinj : Set.InjOn Complex.re (N : Set ℂ) := hinj.mono fun a ha => (hNmem a ha).1
  have hsepre (a b : ℂ) (ha : a ∈ N) (hb : b ∈ N) (h : a.re ≠ b.re) : g ≤ |a.re - b.re| :=
    hsep a (hTmem a (hNmem a ha).1).1 b (hTmem b (hNmem b hb).1).1 (fun heq => h (by rw [heq]))
      (hNmem a ha).2 (hNmem b hb).2
  have hcomp := sum_inv_mul_le_of_sep (x := x) (x' := x') hgpos rfl (R := R) (Le := Le)
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
      have := (hdist b h1).2
      rwa [abs_of_pos (by linarith only [h2])] at this)
    (by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hb
      have := (hdist b h1).1
      rwa [abs_of_neg (by linarith only [h2]), neg_sub] at this)
  have hRcard : R.card = (N.filter fun b => x' < b.re).card :=
    Finset.card_image_of_injOn (hNinj.mono fun a ha => (Finset.mem_filter.mp ha).1)
  have hLcard : Le.card = (N.filter fun b => b.re < x).card :=
    Finset.card_image_of_injOn (hNinj.mono fun a ha => (Finset.mem_filter.mp ha).1)
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
  -- the count
  have hNcard : (R.card : ℝ) + (Le.card : ℝ) + 2 ≤ n := by
    have hNsum : (N.filter fun b => x' < b.re).card + (N.filter fun b => b.re < x).card = N.card := by
      have hsplit : (N.filter fun b => x' < b.re) ∪ (N.filter fun b => b.re < x) = N := by
        ext b
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (h | h) <;> exact h.1
        · intro hb
          rcases hside b hb with h | h
          · exact Or.inl ⟨hb, h⟩
          · exact Or.inr ⟨hb, h⟩
      have hdisj : Disjoint (N.filter fun b => x' < b.re) (N.filter fun b => b.re < x) :=
        Finset.disjoint_left.mpr fun b h1 h2 => by
          have h3 := (Finset.mem_filter.mp h1).2
          have h4 := (Finset.mem_filter.mp h2).2
          linarith only [h3, h4, hxx']
      rw [← Finset.card_union_of_disjoint hdisj, hsplit]
    have hfull : N.card + 2 = (S.filter fun b => |b.re - x| < ρ).card := by
      have h1 : (S.filter fun b => |b.re - x| < ρ) = insert (x : ℂ) (insert (x' : ℂ) N) := by
        ext b
        simp only [hN, hT, Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨h2, h3⟩
          by_cases h4 : b = (x : ℂ)
          · exact Or.inl h4
          by_cases h5 : b = (x' : ℂ)
          · exact Or.inr (Or.inl h5)
          · exact Or.inr (Or.inr ⟨⟨h5, h4, h2⟩, h3⟩)
        · rintro (rfl | rfl | ⟨⟨-, -, h2⟩, h3⟩)
          · exact ⟨hxS, hxnear⟩
          · exact ⟨hx'S, hx'near⟩
          · exact ⟨h2, h3⟩
      have hx'N : (x' : ℂ) ∉ N := fun h => (hTmem _ (hNmem _ h).1).2.2 rfl
      have hxN : (x : ℂ) ∉ insert (x' : ℂ) N := by
        intro h
        rcases Finset.mem_insert.mp h with h | h
        · exact hne h
        · exact (hTmem _ (hNmem _ h).1).2.1 rfl
      rw [h1, Finset.card_insert_of_notMem hxN, Finset.card_insert_of_notMem hx'N]
    have hall : (R.card : ℝ) + (Le.card : ℝ) + 2 = ((S.filter fun b => |b.re - x| < ρ).card : ℝ) := by
      rw [hRcard, hLcard, ← hfull, ← hNsum]
      push_cast
      ring
    rw [hall]
    exact hcount
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
  have hbound : g ^ 2 * (pairCompression t T x x').re ≤
      2 - 1 / ((R.card : ℝ) + 1) - 1 / ((Le.card : ℝ) + 1) + 2 * E * g ^ 2 := by
    rw [hrecomp, mul_add]
    have h1 := mul_le_mul_of_nonneg_left hcomp hg2.le
    rw [mul_div_cancel₀ _ hg2.ne'] at h1
    have h2 := mul_le_mul_of_nonneg_left hfarsum hg2.le
    linarith only [h1, h2]
  have hRn : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  have hLn : (0 : ℝ) ≤ Le.card := Nat.cast_nonneg _
  have h16 := sixteen_div_le _ _ hRn hLn
  have hsumpos : 0 < (R.card : ℝ) + (Le.card : ℝ) + 2 := by linarith only [hRn, hLn]
  have hmono : 16 / (n : ℝ) ≤ 16 / ((R.card : ℝ) + (Le.card : ℝ) + 2) :=
    div_le_div_of_nonneg_left (by norm_num) hsumpos hNcard
  have hr1 : 4 / ((R.card : ℝ) + 1) = 4 * (1 / ((R.card : ℝ) + 1)) := by ring
  have hr2 : 4 / ((Le.card : ℝ) + 1) = 4 * (1 / ((Le.card : ℝ) + 1)) := by ring
  have h6 : 2 * g * -(K * g) ≤ 2 * g * (Q (x' : ℂ) - Q (x : ℂ)).re :=
    mul_le_mul_of_nonneg_left hQre (by positivity)
  nlinarith only [hre, hbound, h16, hmono, h6, hr1, hr2]

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
