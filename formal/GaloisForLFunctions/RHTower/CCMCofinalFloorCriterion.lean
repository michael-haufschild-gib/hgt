import GaloisForLFunctions.RHTower.CCMNestedFloorNoEvacuation

/-!
# The cofinal floor criterion and the Rayleigh-excess collapse

Two route theorems about the bottom of a nested family of Rayleigh floors.

**The cofinal criterion.**  If the floor tends to zero along *any* apertures tending to infinity,
then the energy is nonnegative on every trial domain.  Conversely a single trial vector with
negative energy pins every later floor uniformly below zero by an explicit `δ`.  These are the
positive and quantitative halves of one statement: the floor limit decides nonnegativity of the
energy on the whole exhaustion.

**The collapse.**  Suppose the ground level `ε₀` is compared with a trial Rayleigh value `r` and a
second level `ε₁` through the excess `d = r - ε₀ ≥ 0` and the gap `Gap = ε₁ - ε₀`, and that the
excess-to-gap ratio is `O(1/λ)`.  Rewriting `Gap = (ε₁ - r) + d` absorbs the excess into itself and
leaves

```text
d ≤ 2 C |ε₁ - r| / λ,
```

so `r → 0` and `ε₁ → 0` force `d → 0` and hence `ε₀ → 0`.  Composed with the cofinal criterion, an
`O(1/λ)` excess-to-gap estimate already yields nonnegativity of the energy — the determinant lane
adds no further implication.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology Set MeasureTheory

variable {V : Type*}

/-! ## The cofinal floor criterion -/

/-- **The cofinal criterion.**  A floor tending to zero along any apertures tending to infinity
forces the energy to be nonnegative on every trial domain. -/
theorem nonneg_of_rayleighFloor_tendsto_zero {Q N : V → ℝ} {D : ℝ → Set V} (a : ℝ)
    (hmono : ∀ {b c : ℝ}, b ≤ c → D b ⊆ D c)
    (hbdd : ∀ b : ℝ, BddBelow (rayleighQuotientSet Q N (D b)))
    (hne : (rayleighQuotientSet Q N (D a)).Nonempty)
    (hNpos : ∀ v ∈ D a, N v ≠ 0 → 0 < N v)
    {ι : Type*} {l : Filter ι} [l.NeBot] {aseq : ι → ℝ}
    (hseq : Tendsto aseq l atTop)
    (hlim : Tendsto (fun i => rayleighFloor Q N (D (aseq i))) l (nhds 0))
    {v : V} (hv : v ∈ D a) (hN : N v ≠ 0) : 0 ≤ Q v :=
  (zero_le_rayleighFloor_iff Q N (hbdd a) hNpos).mp
    (zero_le_rayleighFloor_of_tendsto_zero a hmono hbdd hne hseq hlim) v hv hN

/-- **The quantitative alternative.**  One trial vector with negative energy pins every later floor
uniformly below zero. -/
theorem exists_uniform_negative_rayleighFloor {Q N : V → ℝ} {D : ℝ → Set V}
    (hmono : ∀ {a b : ℝ}, a ≤ b → D a ⊆ D b)
    (hbdd : ∀ b : ℝ, BddBelow (rayleighQuotientSet Q N (D b)))
    {a : ℝ} {v : V} (hv : v ∈ D a) (hN : 0 < N v) (hQ : Q v < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ b : ℝ, a ≤ b → rayleighFloor Q N (D b) ≤ -δ := by
  refine ⟨-(Q v / N v), ?_, fun b hb => ?_⟩
  · have : Q v / N v < 0 := div_neg_of_neg_of_pos hQ hN
    linarith
  · exact rayleighFloor_le_of_witness Q N (hbdd b) (hmono hb hv) hN.ne'
      (by rw [neg_neg])

/-! ## The Rayleigh-excess collapse -/

/-- **The collapse theorem.**  An excess-to-gap ratio of size `O(1/λ)` together with vanishing
trial value and vanishing second level forces the ground level to vanish.  The mechanism is that the
gap contains the excess itself, `Gap = (ε₁ - r) + d`, so for `λ > 2C` half of the excess is absorbed
and the remainder is controlled by `|ε₁ - r|/λ`. -/
theorem tendsto_ground_zero_of_excess_gap_ratio
    {eps0 eps1 r : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hd : ∀ lam : ℝ, eps0 lam ≤ r lam)
    (hbound : ∀ᶠ lam : ℝ in atTop,
      r lam - eps0 lam ≤ C * (eps1 lam - eps0 lam) / lam)
    (hr : Tendsto r atTop (nhds 0)) (he1 : Tendsto eps1 atTop (nhds 0)) :
    Tendsto eps0 atTop (nhds 0) := by
  have hdnn : ∀ lam : ℝ, 0 ≤ r lam - eps0 lam := fun lam => by linarith [hd lam]
  have hkey : ∀ᶠ lam : ℝ in atTop,
      r lam - eps0 lam ≤ 2 * C * |eps1 lam - r lam| / lam := by
    filter_upwards [hbound, eventually_gt_atTop (2 * C), eventually_gt_atTop (0 : ℝ)]
      with lam hb hlam2 hlam0
    have hgapeq : eps1 lam - eps0 lam = (eps1 lam - r lam) + (r lam - eps0 lam) := by ring
    rw [hgapeq, le_div_iff₀ hlam0] at hb
    have habs : eps1 lam - r lam ≤ |eps1 lam - r lam| := le_abs_self _
    have hCabs : C * (eps1 lam - r lam) ≤ C * |eps1 lam - r lam| :=
      mul_le_mul_of_nonneg_left habs hC.le
    have hCd : C * (r lam - eps0 lam) ≤ lam / 2 * (r lam - eps0 lam) :=
      mul_le_mul_of_nonneg_right (by linarith) (hdnn lam)
    rw [le_div_iff₀ hlam0]
    linarith
  have hnum : Tendsto (fun lam : ℝ => 2 * C * |eps1 lam - r lam|) atTop (nhds 0) := by
    have h1 : Tendsto (fun lam : ℝ => eps1 lam - r lam) atTop (nhds 0) := by
      simpa using he1.sub hr
    have h2 : Tendsto (fun lam : ℝ => |eps1 lam - r lam|) atTop (nhds 0) := by
      simpa using h1.abs
    simpa using h2.const_mul (2 * C)
  have hlim : Tendsto (fun lam : ℝ => 2 * C * |eps1 lam - r lam| / lam) atTop (nhds 0) :=
    hnum.div_atTop tendsto_id
  have hdzero : Tendsto (fun lam : ℝ => r lam - eps0 lam) atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall hdnn) hkey hlim
  have hfin : Tendsto (fun lam : ℝ => r lam - (r lam - eps0 lam)) atTop (nhds 0) := by
    simpa using hr.sub hdzero
  have heq : (fun lam : ℝ => r lam - (r lam - eps0 lam)) = eps0 := by
    funext lam; ring
  rw [heq] at hfin
  exact hfin

/-- **The composed chain.**  An `O(1/λ)` excess-to-gap estimate on the floors of a nested family
already forces nonnegativity of the energy on every trial domain. -/
theorem nonneg_of_excess_gap_ratio {Q N : V → ℝ} {D : ℝ → Set V} (a : ℝ)
    (hmono : ∀ {b c : ℝ}, b ≤ c → D b ⊆ D c)
    (hbdd : ∀ b : ℝ, BddBelow (rayleighQuotientSet Q N (D b)))
    (hne : (rayleighQuotientSet Q N (D a)).Nonempty)
    (hNpos : ∀ v ∈ D a, N v ≠ 0 → 0 < N v)
    {eps1 r : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hd : ∀ lam : ℝ, rayleighFloor Q N (D lam) ≤ r lam)
    (hbound : ∀ᶠ lam : ℝ in atTop,
      r lam - rayleighFloor Q N (D lam)
        ≤ C * (eps1 lam - rayleighFloor Q N (D lam)) / lam)
    (hr : Tendsto r atTop (nhds 0)) (he1 : Tendsto eps1 atTop (nhds 0))
    {v : V} (hv : v ∈ D a) (hN : N v ≠ 0) : 0 ≤ Q v := by
  have hcollapse : Tendsto (fun lam : ℝ => rayleighFloor Q N (D lam)) atTop (nhds 0) :=
    tendsto_ground_zero_of_excess_gap_ratio hC hd hbound hr he1
  exact nonneg_of_rayleighFloor_tendsto_zero a hmono hbdd hne hNpos
    (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop) hcollapse hv hN

/-! ## The aperture-restricted instantiation -/

/-- **The cofinal criterion for the restricted kernel form.**  If the restricted kernel floor tends
to zero along apertures tending to infinity, the kernel form is nonnegative on every compactly
supported trial function. -/
theorem diffBilinForm_nonneg_of_restrictedKernelFloor_tendsto_zero (K : ℝ → ℝ)
    (hbdd : ∀ a : ℝ, BddBelow
      (rayleighQuotientSet (fun v => diffBilinForm K v v) sqMass (apertureDomain a)))
    {a : ℝ} (ha : 0 < a)
    (hNpos : ∀ v ∈ apertureDomain a, sqMass v ≠ 0 → 0 < sqMass v)
    {ι : Type*} {l : Filter ι} [l.NeBot] {aseq : ι → ℝ}
    (hseq : Tendsto aseq l atTop)
    (hlim : Tendsto (fun i => restrictedKernelFloor K (aseq i)) l (nhds 0))
    {v : ℝ → ℝ} (hv : v ∈ apertureDomain a) (hN : sqMass v ≠ 0) :
    0 ≤ diffBilinForm K v v :=
  nonneg_of_rayleighFloor_tendsto_zero a (fun h => apertureDomain_mono h) hbdd
    (rayleighQuotientSet_apertureDomain_nonempty K ha) hNpos hseq hlim hv hN

/-- **The quantitative alternative for the restricted kernel form.**  One compactly supported test
with negative energy pins every later restricted floor uniformly below zero. -/
theorem exists_uniform_negative_restrictedKernelFloor (K : ℝ → ℝ)
    (hbdd : ∀ b : ℝ, BddBelow
      (rayleighQuotientSet (fun v => diffBilinForm K v v) sqMass (apertureDomain b)))
    {a : ℝ} {v : ℝ → ℝ} (hv : v ∈ apertureDomain a) (hN : 0 < sqMass v)
    (hQ : diffBilinForm K v v < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ b : ℝ, a ≤ b → restrictedKernelFloor K b ≤ -δ :=
  exists_uniform_negative_rayleighFloor (fun h => apertureDomain_mono h) hbdd hv hN hQ

end GaloisForLFunctions.RHTower

end
