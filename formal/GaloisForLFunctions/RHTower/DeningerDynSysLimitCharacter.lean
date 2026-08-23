import GaloisForLFunctions.RHTower.DeningerDynSysPowerLimit
import GaloisForLFunctions.RHTower.DeningerDynSysNoSmallSubgroups

/-!
# Characters of the projective limit along the power maps

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 3.6
(`t37n`).

The projective limit `lim_{N₀} M` of a commutative group along the power maps is again a group,
and it is `ν`-divisible for every `ν ∈ N₀`: the shifted family `(x_{μ ν})_μ` is a `ν`-th root of
`x`.  Consequently a character of the limit is determined by its `ν`-th power, which is the
inverse of the Frobenius operator used by Deninger.

A continuous character into a group with no small subgroups kills `ker pr_λ` for some `λ ∈ N₀`:
the kernels of the projections form a neighbourhood basis of subgroups of the identity, because
`x_λ = 1` forces `x_ν = 1` for every divisor `ν` of `λ`.
-/

namespace RHTower

variable {M : Type*} [CommGroup M] {N₀ : Submonoid ℕ}

/-- The projective limit of a commutative group is a group. -/
instance deningerPowerLimitCommGroup : CommGroup (DeningerPowerLimit M N₀) :=
  { (inferInstance : CommMonoid (DeningerPowerLimit M N₀)) with
    inv := fun x => ⟨fun ν => (x.1 ν)⁻¹, fun ν μ => by
      show (x.1 (ν * μ))⁻¹ ^ (μ : ℕ) = (x.1 ν)⁻¹
      rw [inv_pow, x.2 ν μ]⟩
    inv_mul_cancel := fun x => by
      apply Subtype.ext
      funext ν
      exact inv_mul_cancel _ }

@[simp] theorem deningerPowerLimit_inv_apply (x : DeningerPowerLimit M N₀) (ν : N₀) :
    (x⁻¹).1 ν = (x.1 ν)⁻¹ := rfl

/-! ## Divisibility of the limit -/

/-- The shift `(x_μ) ↦ (x_{μ ν})`, a `ν`-th root on the projective limit. -/
def deningerPowerShift (ν : N₀) (x : DeningerPowerLimit M N₀) : DeningerPowerLimit M N₀ :=
  ⟨fun μ => x.1 (μ * ν), by
    intro μ ρ
    show x.1 (μ * ρ * ν) ^ (ρ : ℕ) = x.1 (μ * ν)
    rw [mul_right_comm μ ρ ν]
    exact x.2 (μ * ν) ρ⟩

@[simp] theorem deningerPowerShift_apply (ν : N₀) (x : DeningerPowerLimit M N₀) (μ : N₀) :
    (deningerPowerShift ν x).1 μ = x.1 (μ * ν) := rfl

/-- **The projective limit is `ν`-divisible for every `ν ∈ N₀`.** -/
theorem deningerPowerShift_pow (ν : N₀) (x : DeningerPowerLimit M N₀) :
    deningerPowerShift ν x ^ (ν : ℕ) = x := by
  apply Subtype.ext
  funext μ
  show x.1 (μ * ν) ^ (ν : ℕ) = x.1 μ
  exact x.2 μ ν

/-- **Deninger, §3.**  A character of the projective limit is determined by its `ν`-th power for
`ν ∈ N₀`; this is the injectivity of the Frobenius operator `F_ν`. -/
theorem deningerLimitChar_pow_injective {C : Type*} [CommMonoid C] {ν : N₀}
    {χ ψ : DeningerPowerLimit M N₀ →* C}
    (h : ∀ x : DeningerPowerLimit M N₀, χ x ^ (ν : ℕ) = ψ x ^ (ν : ℕ)) : χ = ψ := by
  ext x
  have hx := h (deningerPowerShift ν x)
  rwa [← map_pow, ← map_pow, deningerPowerShift_pow] at hx

/-! ## Kernels of the projections -/

variable [TopologicalSpace M]

omit [TopologicalSpace M] in
/-- If `lam = ν * μ` with `μ ∈ N₀` then `x_lam = 1` forces `x_ν = 1`. -/
theorem deningerPowerLimit_eq_one_of_mul {x : DeningerPowerLimit M N₀} {ν μ : N₀}
    (h : x.1 (ν * μ) = 1) : x.1 ν = 1 := by
  have hx := x.2 ν μ
  rw [h, one_pow] at hx
  exact hx.symm

/-- **Deninger, Proposition 3.6 (`t37n`), the key step.**  A continuous character of the
projective limit into a group with no small subgroups is trivial on the kernel of some
projection. -/
theorem deningerLimit_ker_proj_le_ker {C : Type*} [CommGroup C] [TopologicalSpace C]
    (hns : DeningerNoSmallSubgroups C) (χ : DeningerPowerLimit M N₀ →* C)
    (hχ : Continuous χ) :
    ∃ lam : N₀, ∀ x : DeningerPowerLimit M N₀, x.1 lam = 1 → χ x = 1 := by
  classical
  obtain ⟨U, hU, hUsub⟩ := hns
  have hpre : χ ⁻¹' U ∈ nhds (1 : DeningerPowerLimit M N₀) := by
    refine hχ.continuousAt.preimage_mem_nhds ?_
    rwa [map_one]
  rw [nhds_induced (fun (x : DeningerPowerLimit M N₀) => (x.1 : N₀ → M)) 1,
    Filter.mem_comap] at hpre
  obtain ⟨V, hV, hVU⟩ := hpre
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, hIfin, t, ht, hIt⟩ := hV
  refine ⟨∏ ν ∈ hIfin.toFinset, ν, ?_⟩
  intro x hx
  have hprod : ∀ (y : DeningerPowerLimit M N₀),
      y.1 (∏ ν ∈ hIfin.toFinset, ν) = 1 → ∀ ν ∈ I, y.1 ν = 1 := by
    intro y hy ν hν
    have hmem : ν ∈ hIfin.toFinset := hIfin.mem_toFinset.2 hν
    have hsplit : ν * (∏ μ ∈ hIfin.toFinset.erase ν, μ) = ∏ μ ∈ hIfin.toFinset, μ :=
      Finset.mul_prod_erase hIfin.toFinset (fun μ : N₀ => μ) hmem
    refine deningerPowerLimit_eq_one_of_mul (μ := ∏ μ ∈ hIfin.toFinset.erase ν, μ) ?_
    rw [hsplit]
    exact hy
  have hker : ∀ ν ∈ I, x.1 ν = 1 := hprod x hx
  have hxV : (x.1 : N₀ → M) ∈ V := by
    refine hIt ?_
    intro ν hν
    rw [hker ν hν]
    exact mem_of_mem_nhds (ht ν)
  have hxU : χ x ∈ U := hVU hxV
  -- the kernel of the projection is a subgroup, so its image is a subgroup inside `U`
  have hsub : ((MonoidHom.ker (deningerPowerProj (M := M)
      (∏ ν ∈ hIfin.toFinset, ν))).map χ : Subgroup C) = ⊥ := by
    refine hUsub _ ?_
    rintro _ ⟨z, hz, rfl⟩
    have hz1 : z.1 (∏ ν ∈ hIfin.toFinset, ν) = 1 := hz
    have hzV : (z.1 : N₀ → M) ∈ V := by
      refine hIt ?_
      intro ν hν
      have hz2 : z.1 ν = 1 := hprod z hz1 ν hν
      rw [hz2]
      exact mem_of_mem_nhds (ht ν)
    exact hVU hzV
  have hmem : χ x ∈ (MonoidHom.ker (deningerPowerProj (M := M)
      (∏ ν ∈ hIfin.toFinset, ν))).map χ := ⟨x, hx, rfl⟩
  rw [hsub] at hmem
  simpa using hmem

end RHTower

namespace RHTower

variable {M : Type*} [CommGroup M] {N₀ : Submonoid ℕ} [TopologicalSpace M]

/-- **Deninger, Proposition 3.6 (`t37n`).**  A continuous character of the projective limit
`lim_{N₀} κˣ` into a group with no small subgroups and divisible — for instance `Cˣ` for an
algebraically closed topological field `C` — is of the form `ψ ∘ pr_λ` for some `λ ∈ N₀` and some
character `ψ` of `κˣ`. -/
theorem deningerLimitChar_factors {C : Type*} [CommGroup C] [TopologicalSpace C]
    [RootableBy C ℕ] (hns : DeningerNoSmallSubgroups C)
    (χ : DeningerPowerLimit M N₀ →* C) (hχ : Continuous χ) :
    ∃ (lam : N₀) (ψ : M →* C), χ = ψ.comp (deningerPowerProj lam) := by
  obtain ⟨lam, hlam⟩ := deningerLimit_ker_proj_le_ker hns χ hχ
  set pr := deningerPowerProj (M := M) lam with hpr
  have hker : MonoidHom.ker pr ≤ MonoidHom.ker χ := by
    intro z hz
    exact hlam z hz
  set φ : (DeningerPowerLimit M N₀ ⧸ MonoidHom.ker pr) →* C :=
    QuotientGroup.lift (MonoidHom.ker pr) χ hker with hφ
  set e : (DeningerPowerLimit M N₀ ⧸ MonoidHom.ker pr) ≃* pr.range :=
    QuotientGroup.quotientKerEquivRange pr with he
  set ψ₀ : pr.range →* C := φ.comp (e.symm : pr.range →* _) with hψ₀
  obtain ⟨ψ, hψ⟩ := deningerExtend_of_rootableBy (pr.range).subtype Subtype.val_injective ψ₀
  refine ⟨lam, ψ, ?_⟩
  ext x
  have hmem : pr x ∈ pr.range := ⟨x, rfl⟩
  have h1 : ψ (pr x) = ψ₀ ⟨pr x, hmem⟩ := by
    have := congrArg (fun g : pr.range →* C => g ⟨pr x, hmem⟩) hψ
    simpa using this
  have h2 : e (QuotientGroup.mk x) = ⟨pr x, hmem⟩ := rfl
  have h3 : ψ₀ ⟨pr x, hmem⟩ = φ (QuotientGroup.mk x) := by
    rw [hψ₀]
    show φ (e.symm ⟨pr x, hmem⟩) = φ (QuotientGroup.mk x)
    rw [← h2, MulEquiv.symm_apply_apply]
  have h4 : φ (QuotientGroup.mk x) = χ x := rfl
  show χ x = ψ (pr x)
  rw [h1, h3, h4]

/-- **Deninger, Corollary 3.7 (`t38n`).**  If `κˣ` carries the discrete topology and `Cˣ` has no
small subgroups, the continuous characters of `lim_{N₀} κˣ` are exactly those factoring through a
projection. -/
theorem deningerLimitChar_continuous_iff [DiscreteTopology M] {C : Type*} [CommGroup C]
    [TopologicalSpace C] [RootableBy C ℕ] (hns : DeningerNoSmallSubgroups C)
    (χ : DeningerPowerLimit M N₀ →* C) :
    Continuous χ ↔ ∃ (lam : N₀) (ψ : M →* C), χ = ψ.comp (deningerPowerProj lam) := by
  constructor
  · intro hχ
    exact deningerLimitChar_factors hns χ hχ
  · rintro ⟨lam, ψ, rfl⟩
    exact (continuous_of_discreteTopology (f := ψ)).comp (deningerPowerProj_continuous lam)

end RHTower
