import Mathlib.RingTheory.Perfection
import Mathlib.Topology.Algebra.Monoid

/-!
# The perfection of a topological monoid, and density of the perfection of a dense submonoid

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 14.7(a).

The perfection `lim_{()^p} M` of a topological monoid carries the projective limit topology, i.e.
the topology induced by the coefficient maps.  If the `p`-th power map is surjective on `M` then
every coefficient map `lim_{()^p} M → M` is surjective, and consequently, for a homomorphism
`φ : M → N` with dense image into a topological monoid `N`, the induced map
`lim_{()^p} M → lim_{()^p} N` again has dense image.

Deninger applies this to a ring `A` in which every element is a `p`-th power and its `p`-adic
completion `Â`: the image of `lim_{()^p} A` in `lim_{()^p} Â` is dense.  The mechanism is that a
neighbourhood in the projective limit is controlled by a single coefficient, because the earlier
coefficients are `p`-power images of the later ones.
-/

namespace RHTower

open Perfection

variable {M N : Type*} [CommMonoid M] [CommMonoid N] {p : ℕ}

/-- A later coefficient of an element of the perfection determines every earlier one. -/
theorem deningerPerfection_coeff_pow (x : Perfection M p) (i k : ℕ) :
    coeffMonoidHom M p (i + k) x ^ p ^ k = coeffMonoidHom M p i x := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
      have h : coeffMonoidHom M p (i + 1 + k) x ^ p ^ k = coeffMonoidHom M p (i + 1) x := ih (i + 1)
      have hx : coeffMonoidHom M p (i + 1) x ^ p = coeffMonoidHom M p i x := x.2 i
      calc coeffMonoidHom M p (i + (k + 1)) x ^ p ^ (k + 1)
          = (coeffMonoidHom M p (i + 1 + k) x ^ p ^ k) ^ p := by
            rw [show i + (k + 1) = i + 1 + k from by omega, ← pow_mul, ← pow_succ]
        _ = coeffMonoidHom M p i x := by rw [h, hx]

/-- **Deninger, Proposition 14.7(a), first step.**  If the `p`-th power map is surjective on `M`,
every coefficient of the perfection is surjective. -/
theorem deningerPerfection_coeffMonoidHom_surjective
    (hp : ∀ a : M, ∃ b : M, b ^ p = a) (n : ℕ) :
    Function.Surjective (coeffMonoidHom M p n) := by
  classical
  intro a
  choose r hr using hp
  refine ⟨⟨fun k => if k ≤ n then a ^ p ^ (n - k) else r^[k - n] a, ?_⟩, ?_⟩
  · intro k
    by_cases hk1 : k + 1 ≤ n
    · have hk : k ≤ n := by omega
      simp only [if_pos hk1, if_pos hk, ← pow_mul, ← pow_succ]
      congr 2
      omega
    · by_cases hk : k ≤ n
      · have hkn : k = n := by omega
        subst hkn
        simp only [if_neg hk1, if_pos (le_refl k)]
        have : k + 1 - k = 1 := by omega
        rw [this]
        simpa using hr a
      · simp only [if_neg hk1, if_neg hk]
        have h1 : k + 1 - n = (k - n) + 1 := by omega
        rw [h1, Function.iterate_succ_apply']
        exact hr _
  · show (if n ≤ n then a ^ p ^ (n - n) else r^[n - n] a) = a
    simp

variable [TopologicalSpace N]

/-- The projective limit topology on the perfection of a topological monoid. -/
instance deningerPerfectionTopology : TopologicalSpace (Perfection N p) :=
  TopologicalSpace.induced (fun x (n : ℕ) => coeffMonoidHom N p n x) inferInstance

theorem deningerPerfection_continuous_coeff (n : ℕ) :
    Continuous (coeffMonoidHom N p n) :=
  (continuous_apply n).comp (continuous_induced_dom)

/-- **Deninger, Proposition 14.7(a).**  If every element of `M` is a `p`-th power and `φ : M → N`
has dense image in a topological monoid `N`, then the induced map of perfections has dense image.
Applied to a ring `A` in which every element is a `p`-th power and its `p`-adic completion, this is
the density assertion of Proposition 14.7(a). -/
theorem deningerPerfection_denseRange_mapMonoidHom [ContinuousMul N]
    (hp : ∀ a : M, ∃ b : M, b ^ p = a) (φ : M →* N) (hφ : DenseRange φ) :
    DenseRange (mapMonoidHom p φ) := by
  classical
  intro y
  rw [mem_closure_iff_nhds]
  intro U hU
  rw [nhds_induced (fun (x : Perfection N p) (n : ℕ) => coeffMonoidHom N p n x) y,
    Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, hIfin, t, ht, hIt⟩ := hV
  obtain ⟨n, hn⟩ := hIfin.bddAbove
  set c : N := coeffMonoidHom N p n y with hc
  have hcoeff : ∀ i ∈ I, c ^ p ^ (n - i) = coeffMonoidHom N p i y := by
    intro i hi
    have hin : i ≤ n := hn hi
    have := deningerPerfection_coeff_pow (p := p) y i (n - i)
    rwa [show i + (n - i) = n from by omega] at this
  have hW : (⋂ i ∈ I, (fun d : N => d ^ p ^ (n - i)) ⁻¹' t i) ∈ nhds c := by
    refine (Filter.biInter_mem hIfin).2 ?_
    intro i hi
    refine ContinuousAt.preimage_mem_nhds (Continuous.continuousAt (continuous_pow _)) ?_
    rw [hcoeff i hi]
    exact ht i
  obtain ⟨d, hdW, a, rfl⟩ := mem_closure_iff_nhds.1 (hφ c) _ hW
  obtain ⟨x, hx⟩ := deningerPerfection_coeffMonoidHom_surjective (p := p) hp n a
  refine ⟨mapMonoidHom p φ x, hVU ?_, ⟨x, rfl⟩⟩
  refine hIt ?_
  intro i hi
  have hin : i ≤ n := hn hi
  have hxi : coeffMonoidHom M p i x = a ^ p ^ (n - i) := by
    have := deningerPerfection_coeff_pow (p := p) x i (n - i)
    rw [show i + (n - i) = n from by omega, hx] at this
    exact this.symm
  have : coeffMonoidHom N p i (mapMonoidHom p φ x) = φ a ^ p ^ (n - i) := by
    rw [coeffMonoidHom_mapMonoidHom, hxi, map_pow]
  have hmem := Set.mem_iInter₂.1 hdW i hi
  show coeffMonoidHom N p i (mapMonoidHom p φ x) ∈ t i
  rw [this]
  exact hmem

end RHTower
