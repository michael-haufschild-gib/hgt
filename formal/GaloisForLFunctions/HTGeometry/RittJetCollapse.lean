import GaloisForLFunctions.HTGeometry.RittLinearizerJets

/-!
# An algebraic top jet of a linearizer already lies in the prefix field

Let `τ` solve `σ τ = q · τ` in a Ritt frame and let `E` be a `σ`-stable intermediate field
containing `τ` and the derivatives `d τ, …, d^[m] τ`, and containing every `σ`-invariant of the
ambient field.

The weight element `z = (d τ) ^ (m+1) · τ ^ (−m)` lies in `E` and is a multiplicative shift
coordinate with the same multiplier `q / ρ ^ (m+1)` that jet triangularity attaches to
`d^[m+1] τ`.  The ratio `d^[m+1] τ / z` therefore solves an *inhomogeneous* first-order shift
equation with increment in `E`, so additive rigidity upgrades "algebraic over `E`" to "in `E`":

`d^[m+1] τ` integral over `E`  ⟹  `d^[m+1] τ ∈ E`.

This is the collapse step of the Galoisian proof of Ritt's theorem: the tower of jets of a
differentially algebraic linearizer acquires no new unipotent layer above the first algebraic one.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **The collapse step.**  A top jet of a linearizer that is integral over a `σ`-stable
intermediate field carrying all the lower jets already belongs to that field. -/
theorem jet_mem_of_isIntegral_of_lower_jets_mem (Fr : RittFrame K L) [CharZero L]
    {τ : L} {q : K} (hτ : τ ≠ 0) (hdτ : Fr.d τ ≠ 0) (hq : q ≠ 0) (hqconst : Fr.dK q = 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ)
    {E : IntermediateField K L}
    (hEσ : ∀ x ∈ E, Fr.σ x ∈ E)
    (hEfix : ∀ y : L, Fr.σ y = y → y ∈ E)
    (hτE : τ ∈ E) {m : ℕ} (hm : 1 ≤ m)
    (hjets : ∀ j, j < m → Fr.d^[j + 1] τ ∈ E)
    (hint : IsIntegral ↥E (Fr.d^[m + 1] τ)) :
    Fr.d^[m + 1] τ ∈ E := by
  classical
  haveI : CharZero ↥E := (algebraMap ↥E L).charZero
  have hdτE : Fr.d τ ∈ E := by simpa using hjets 0 hm
  set Q : K := q / Fr.ρ ^ (m + 1) with hQdef
  have hQ0 : Q ≠ 0 := div_ne_zero hq (pow_ne_zero _ Fr.ρ_ne)
  have hQL : algebraMap K L Q ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hQ0
  -- the lower-order defect
  have hvmem := Fr.shift_jet_sub_mem_jetSpan hqconst hshift m
  set v : L := Fr.σ (Fr.d^[m + 1] τ) - algebraMap K L Q * Fr.d^[m + 1] τ with hvdef
  have hvE : v ∈ E := by
    have hspan : ∀ x ∈ Fr.jetSpan τ m, x ∈ E := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨j, hj, rfl⟩ := hy
          exact hjets j hj
      | zero => exact zero_mem E
      | add a b _ _ ha hb => exact add_mem ha hb
      | smul c a _ ha =>
          rw [Algebra.smul_def]
          exact mul_mem (IntermediateField.algebraMap_mem E c) ha
    exact hspan v hvmem
  -- the weight element
  set z : L := (Fr.d τ) ^ ((m : ℤ) + 1) * τ ^ (-(m : ℤ)) with hzdef
  have hz0 : z ≠ 0 := mul_ne_zero (zpow_ne_zero _ hdτ) (zpow_ne_zero _ hτ)
  have hzE : z ∈ E := mul_mem (zpow_mem hdτE _) (zpow_mem hτE _)
  have hσz : Fr.σ z = algebraMap K L Q * z := by
    have hd := Fr.sigma_d_eq_of_shift hqconst hshift
    have hcoef : ((q / Fr.ρ) ^ ((m : ℤ) + 1)) * (q ^ (-(m : ℤ))) = Q := by
      have hcast : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hQdef, div_zpow, zpow_neg, hcast]
      simp only [zpow_natCast]
      field_simp
      ring
    rw [hzdef, map_mul, map_zpow₀, map_zpow₀, hd, hshift, mul_zpow, mul_zpow, ← map_zpow₀,
      ← map_zpow₀, ← hcoef, map_mul]
    ring
  -- the unipotent ratio
  set ω : L := Fr.d^[m + 1] τ / z with hωdef
  have hc : Fr.σ ω = ω + v / (algebraMap K L Q * z) := by
    have hexp : Fr.σ (Fr.d^[m + 1] τ) = algebraMap K L Q * Fr.d^[m + 1] τ + v := by
      rw [hvdef]; ring
    rw [hωdef, map_div₀, hexp, hσz]
    field_simp
  have hcE : v / (algebraMap K L Q * z) ∈ E :=
    div_mem hvE (mul_mem (IntermediateField.algebraMap_mem E Q) hzE)
  -- additive rigidity over the intermediate field
  have hcomp : ∀ a : ↥E, Fr.σ (algebraMap ↥E L a) = algebraMap ↥E L
      (⟨Fr.σ (a : L), hEσ (a : L) a.2⟩ : ↥E) := fun _ => rfl
  have hfix : ∀ y : L, Fr.σ y = y → ∃ a : ↥E, algebraMap ↥E L a = y :=
    fun y hy => ⟨⟨y, hEfix y hy⟩, rfl⟩
  have hintω : IsIntegral ↥E ω := by
    have hzinv : z⁻¹ = algebraMap ↥E L (⟨z, hzE⟩ : ↥E)⁻¹ := by
      rw [map_inv₀]
      rfl
    rw [hωdef, div_eq_mul_inv, hzinv]
    exact hint.mul (isIntegral_algebraMap)
  obtain ⟨a, ha⟩ :=
    exists_algebraMap_eq_of_isIntegral_of_shift_add Fr.σ
      ({ toFun := fun a : ↥E => ⟨Fr.σ (a : L), hEσ (a : L) a.2⟩
         map_one' := by ext; simp
         map_mul' := fun _ _ => by ext; simp
         map_zero' := by ext; simp
         map_add' := fun _ _ => by ext; simp } : ↥E →+* ↥E)
      hcomp hfix (c := (⟨v / (algebraMap K L Q * z), hcE⟩ : ↥E)) hc hintω
  have hωE : ω ∈ E := by rw [← ha]; exact (a : ↥E).2
  have : Fr.d^[m + 1] τ = ω * z := by
    rw [hωdef]
    field_simp
  rw [this]
  exact mul_mem hωE hzE

end GaloisForLFunctions.HTGeometry
