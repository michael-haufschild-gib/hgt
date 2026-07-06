/-
# Existence of the gap equilibrium via pole blow-up

The deviation identity (`cothField_theta_deviation`) characterizes the equilibrium `x*` by
`F(x*) = L`. Here that root is shown to **exist** in every pole-free gap whose two endpoints are simple
poles — completing the field as an object. The field blows up at the endpoints: at the left pole
`F(x) → +∞` as `x → a⁺` (the term `rcoth((x−a)/2) ≥ 2/(x−a) → +∞`, the rest continuous), and
`F(x) → −∞` as `x → b⁻`; the intermediate value theorem (`cothField_exists_equilibrium`) then attains
every level. Instantiated on the harmonic model, this gives the equilibrium — hence the deviation
identity holds for a genuine root, not a hypothetical one.

`rcoth_shift_atTop`, `rcoth_shift_atBot`, `cothField_atTop_leftPole`, `cothField_atBot_rightPole`,
`cothField_root_exists`, `harmonic_equilibrium_exists`, `harmonic_theta_deviation_exists`.
-/
import GaloisForLFunctions.RHTower.LegStripHarmonic
open Real Set Filter Topology
noncomputable section
namespace RHTower

/-- `rcoth((x−a)/2) → +∞` as `x → a⁺`: bounded below by `2/(x−a) → +∞`. -/
theorem rcoth_shift_atTop (a : ℝ) :
    Tendsto (fun x => rcoth ((x - a)/2)) (𝓝[>] a) atTop := by
  have hφ : Tendsto (fun x : ℝ => x - a) (𝓝[>] a) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h : Tendsto (fun x : ℝ => x - a) (𝓝 a) (𝓝 0) := by
        have := (continuous_sub_right a).tendsto a; simpa using this
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [mem_Ioi] at hx ⊢; linarith
  have hinv : Tendsto (fun x : ℝ => (x - a)⁻¹) (𝓝[>] a) atTop := tendsto_inv_nhdsGT_zero.comp hφ
  have h2 : Tendsto (fun x : ℝ => 2 * (x - a)⁻¹) (𝓝[>] a) atTop := hinv.const_mul_atTop (by norm_num)
  apply tendsto_atTop_mono' _ _ h2
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [mem_Ioi] at hx
  have hpos : 0 < (x - a)/2 := by linarith
  have hle := inv_le_rcoth hpos
  rw [one_div] at hle
  rwa [show (2 : ℝ) * (x - a)⁻¹ = ((x - a)/2)⁻¹ by rw [inv_div]; ring]

/-- `rcoth((x−b)/2) → −∞` as `x → b⁻`: bounded above by `2/(x−b) → −∞`. -/
theorem rcoth_shift_atBot (b : ℝ) :
    Tendsto (fun x => rcoth ((x - b)/2)) (𝓝[<] b) atBot := by
  have hφ : Tendsto (fun x : ℝ => x - b) (𝓝[<] b) (𝓝[<] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h : Tendsto (fun x : ℝ => x - b) (𝓝 b) (𝓝 0) := by
        have := (continuous_sub_right b).tendsto b; simpa using this
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [mem_Iio] at hx ⊢; linarith
  have hinv : Tendsto (fun x : ℝ => (x - b)⁻¹) (𝓝[<] b) atBot := tendsto_inv_nhdsLT_zero.comp hφ
  have h2 : Tendsto (fun x : ℝ => 2 * (x - b)⁻¹) (𝓝[<] b) atBot := hinv.const_mul_atBot (by norm_num)
  apply tendsto_atBot_mono' _ _ h2
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [mem_Iio] at hx
  have hbx : x - b ≠ 0 := by intro hc; linarith [sub_eq_zero.mp hc]
  have hle : rcoth ((x - b)/2) ≤ 1/((x - b)/2) := by
    have h1 := inv_le_rcoth (show 0 < -((x - b)/2) by linarith)
    rw [one_div] at h1
    rw [rcoth_neg, inv_neg] at h1
    have : rcoth ((x - b)/2) ≤ ((x - b)/2)⁻¹ := by linarith
    rwa [← one_div] at this
  rwa [show (2 : ℝ) * (x - b)⁻¹ = 1/((x - b)/2) by field_simp]

/-- **Left-endpoint blow-up.** With a simple pole at `a` (`t k0 = a`, no other pole at `a`), the field
`→ +∞` as `x → a⁺`: the term `rcoth((x−a)/2) → +∞`, the rest continuous. -/
theorem cothField_atTop_leftPole {ι : Type*} (s : Finset ι) (t : ι → ℝ) {a : ℝ}
    {k0 : ι} (hk0 : k0 ∈ s) (hk0a : t k0 = a)
    (hsimple : ∀ k ∈ s, k ≠ k0 → t k ≠ a) :
    Tendsto (cothField s t) (𝓝[>] a) atTop := by
  classical
  have hsplit : cothField s t
      = fun x => rcoth ((x - t k0)/2) + ∑ k ∈ s.erase k0, rcoth ((x - t k)/2) := by
    funext x; rw [cothField, ← Finset.add_sum_erase s _ hk0]
  rw [hsplit]
  have hhead : Tendsto (fun x => rcoth ((x - t k0)/2)) (𝓝[>] a) atTop := by
    rw [hk0a]; exact rcoth_shift_atTop a
  have hrest : Tendsto (fun x => ∑ k ∈ s.erase k0, rcoth ((x - t k)/2)) (𝓝[>] a)
      (𝓝 (∑ k ∈ s.erase k0, rcoth ((a - t k)/2))) := by
    apply tendsto_finsetSum
    intro k hk
    rw [Finset.mem_erase] at hk
    have hka : t k ≠ a := hsimple k hk.2 hk.1
    have hne : (a - t k)/2 ≠ 0 := by
      intro hc; apply hka; have : a - t k = 0 := by linarith
      linarith
    have hcont : ContinuousAt (fun y : ℝ => rcoth ((y - t k)/2)) a := by
      simp only [rcoth]
      exact ContinuousAt.div (by fun_prop) (by fun_prop) (Real.sinh_ne_zero.mpr hne)
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  exact hhead.atTop_add hrest

/-- **Right-endpoint blow-up.** With a simple pole at `b` (`t k1 = b`, no other pole at `b`), the field
`→ −∞` as `x → b⁻`. -/
theorem cothField_atBot_rightPole {ι : Type*} (s : Finset ι) (t : ι → ℝ) {b : ℝ}
    {k1 : ι} (hk1 : k1 ∈ s) (hk1b : t k1 = b)
    (hsimple : ∀ k ∈ s, k ≠ k1 → t k ≠ b) :
    Tendsto (cothField s t) (𝓝[<] b) atBot := by
  classical
  have hsplit : cothField s t
      = fun x => rcoth ((x - t k1)/2) + ∑ k ∈ s.erase k1, rcoth ((x - t k)/2) := by
    funext x; rw [cothField, ← Finset.add_sum_erase s _ hk1]
  rw [hsplit]
  have hhead : Tendsto (fun x => rcoth ((x - t k1)/2)) (𝓝[<] b) atBot := by
    rw [hk1b]; exact rcoth_shift_atBot b
  have hrest : Tendsto (fun x => ∑ k ∈ s.erase k1, rcoth ((x - t k)/2)) (𝓝[<] b)
      (𝓝 (∑ k ∈ s.erase k1, rcoth ((b - t k)/2))) := by
    apply tendsto_finsetSum
    intro k hk
    rw [Finset.mem_erase] at hk
    have hkb : t k ≠ b := hsimple k hk.2 hk.1
    have hne : (b - t k)/2 ≠ 0 := by
      intro hc; apply hkb; have : b - t k = 0 := by linarith
      linarith
    have hcont : ContinuousAt (fun y : ℝ => rcoth ((y - t k)/2)) b := by
      simp only [rcoth]
      exact ContinuousAt.div (by fun_prop) (by fun_prop) (Real.sinh_ne_zero.mpr hne)
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  exact hhead.atBot_add hrest

/-- **Existence of the gap equilibrium.** In a pole-free gap `(a,b)` with simple poles at both
endpoints, the field attains every level `L` at some interior point (blow-ups `+∞/−∞` at the ends,
IVT). With `cothField_eq_unique` the root is unique. -/
theorem cothField_root_exists {ι : Type*} (s : Finset ι) (t : ι → ℝ) {a b : ℝ} (hab : a < b)
    (hpoles : ∀ k ∈ s, t k ≤ a ∨ b ≤ t k)
    {k0 : ι} (hk0 : k0 ∈ s) (hk0a : t k0 = a) (hsimple0 : ∀ k ∈ s, k ≠ k0 → t k ≠ a)
    {k1 : ι} (hk1 : k1 ∈ s) (hk1b : t k1 = b) (hsimple1 : ∀ k ∈ s, k ≠ k1 → t k ≠ b)
    (L : ℝ) : ∃ x ∈ Ioo a b, cothField s t x = L := by
  have hT := cothField_atTop_leftPole s t hk0 hk0a hsimple0
  have hB := cothField_atBot_rightPole s t hk1 hk1b hsimple1
  have hmid : a < (a + b)/2 := by linarith
  have hmid' : (a + b)/2 < b := by linarith
  obtain ⟨xlo, hxlo1, hxlo2, hxloF⟩ : ∃ xlo, a < xlo ∧ xlo < (a + b)/2 ∧ L ≤ cothField s t xlo := by
    have h1 : ∀ᶠ x in 𝓝[>] a, L ≤ cothField s t x := hT.eventually_ge_atTop L
    have h2 : ∀ᶠ x in 𝓝[>] a, x < (a + b)/2 := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hmid)] with x hx using hx
    have h3 : ∀ᶠ x in 𝓝[>] a, a < x := by
      filter_upwards [self_mem_nhdsWithin] with x hx; exact hx
    obtain ⟨x, ⟨hxF, hxlt⟩, hxgt⟩ := ((h1.and h2).and h3).exists
    exact ⟨x, hxgt, hxlt, hxF⟩
  obtain ⟨xhi, hxhi1, hxhi2, hxhiF⟩ : ∃ xhi, (a + b)/2 < xhi ∧ xhi < b ∧ cothField s t xhi ≤ L := by
    have h1 : ∀ᶠ x in 𝓝[<] b, cothField s t x ≤ L := hB.eventually_le_atBot L
    have h2 : ∀ᶠ x in 𝓝[<] b, (a + b)/2 < x := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hmid')] with x hx using hx
    have h3 : ∀ᶠ x in 𝓝[<] b, x < b := by
      filter_upwards [self_mem_nhdsWithin] with x hx; exact hx
    obtain ⟨x, ⟨hxF, hxgt⟩, hxlt⟩ := ((h1.and h2).and h3).exists
    exact ⟨x, hxgt, hxlt, hxF⟩
  have hxlo_mem : xlo ∈ Ioo a b := ⟨hxlo1, by linarith⟩
  have hxhi_mem : xhi ∈ Ioo a b := ⟨by linarith, hxhi2⟩
  obtain ⟨x, hxIcc, hxeq⟩ := cothField_exists_equilibrium s t hpoles hxlo_mem hxhi_mem
    (by linarith) hxhiF hxloF
  exact ⟨x, ⟨lt_of_lt_of_le hxlo1 hxIcc.1, lt_of_le_of_lt hxIcc.2 hxhi2⟩, hxeq⟩

/-- **The harmonic equilibrium exists.** On the harmonic model `T_j = c·H_{j−1}` at level `−d`, gap `i`
has an equilibrium: the strictly-increasing poles are simple, so both endpoints are simple poles. -/
theorem harmonic_equilibrium_exists {c : ℝ} (hc : 0 < c) {d i : ℕ} (hid : i + 1 < d) :
    ∃ x ∈ Ioo (harmPole c i) (harmPole c (i+1)),
      cothField (Finset.range d) (harmPole c) x = -(d : ℝ) := by
  have hab : harmPole c i < harmPole c (i+1) := harmPole_strictMono hc (by omega)
  have hpoles : ∀ j ∈ Finset.range d,
      harmPole c j ≤ harmPole c i ∨ harmPole c (i+1) ≤ harmPole c j := by
    intro j _
    rcases Nat.lt_or_ge j (i+1) with h | h
    · exact Or.inl ((harmPole_strictMono hc).monotone (by omega : j ≤ i))
    · exact Or.inr ((harmPole_strictMono hc).monotone h)
  have hi_mem : i ∈ Finset.range d := Finset.mem_range.mpr (by omega)
  have hi1_mem : i + 1 ∈ Finset.range d := Finset.mem_range.mpr (by omega)
  have hinj := (harmPole_strictMono hc).injective
  obtain ⟨x, hx, hxeq⟩ := cothField_root_exists (Finset.range d) (harmPole c) hab hpoles
    hi_mem rfl (fun k _ hk hc' => hk (hinj hc'))
    hi1_mem rfl (fun k _ hk hc' => hk (hinj hc')) (-(d : ℝ))
  exact ⟨x, hx, hxeq⟩

/-- **The field with its equilibrium, complete.** On the harmonic model there is an equilibrium `x*` in
gap `i` whose exact deviation from `½` is `((i+1) + BehindEx − AheadEx)/(W(ξ)·δ_i)`. The equilibrium is
genuine (`harmonic_equilibrium_exists`), so the deviation identity is not conditional on a hypothetical
root. -/
theorem harmonic_theta_deviation_exists {c : ℝ} (hc : 0 < c) {d i : ℕ} (hid : i + 1 < d) :
    ∃ x ∈ Ioo (harmPole c i) (harmPole c (i+1)),
      cothField (Finset.range d) (harmPole c) x = -(d : ℝ)
      ∧ ∃ ξ ∈ Ioo (harmPole c i) (harmPole c (i+1)),
        0 < spurLatticeEnergy (Finset.range d) (harmPole c) ξ
        ∧ 1/2 - (harmPole c (i+1) - x)/(c/((i:ℝ)+1))
          = ((i + 1 : ℝ)
              + (∑ j ∈ (Finset.range d).filter
                  (fun j => harmPole c j < (harmPole c i + harmPole c (i+1))/2),
                  poleExcess ((harmPole c i + harmPole c (i+1))/2 - harmPole c j))
              - ∑ j ∈ (Finset.range d).filter
                  (fun j => (harmPole c i + harmPole c (i+1))/2 < harmPole c j),
                  poleExcess (harmPole c j - (harmPole c i + harmPole c (i+1))/2))
            / (spurLatticeEnergy (Finset.range d) (harmPole c) ξ * (c/((i:ℝ)+1))) := by
  obtain ⟨x, hx, hxeq⟩ := harmonic_equilibrium_exists hc hid
  exact ⟨x, hx, hxeq, harmonic_theta_deviation hc hid hx hxeq⟩

end RHTower
end
