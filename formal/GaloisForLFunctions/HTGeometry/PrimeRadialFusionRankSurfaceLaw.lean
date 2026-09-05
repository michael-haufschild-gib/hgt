import GaloisForLFunctions.HTGeometry.PrimeRadialFusionKolchinRank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The prime-radial fusion rank-surface law

For every radial profile subspace, the dimension visible through valuation cutoff `N` is exactly
the number of leading orders that occur up to `N`.  For a fusion algebra these orders form an
additive semigroup.  Thus the semigroup is not merely an auxiliary invariant: it is the exact
discrete derivative of the relative Kolchin-rank surface of the embedded differential field.
-/

namespace GaloisForLFunctions.HTGeometry

open Set
open scoped Differential

noncomputable section


/-! ## Leading orders of an arbitrary profile subspace -/

/-- A leading formal order realized by a nonzero vector of a radial profile subspace. -/
def PrimeRadialSubspaceOrderOccurs
    (W : Submodule ℂ PrimeRadialProfile) (n : Nat) : Prop :=
  ∃ u : W, u ≠ 0 ∧ (PowerSeries.order (u : PowerSeries ℂ)).toNat = n

theorem primeRadialSubspaceOrderOccurs_iff_coeff
    (W : Submodule ℂ PrimeRadialProfile) (n : Nat) :
    PrimeRadialSubspaceOrderOccurs W n ↔
      ∃ u : W,
        PowerSeries.coeff n (u : PowerSeries ℂ) ≠ 0 ∧
          ∀ i < n, PowerSeries.coeff i (u : PowerSeries ℂ) = 0 := by
  constructor
  · rintro ⟨u, hu, hn⟩
    have hu' : (u : PowerSeries ℂ) ≠ 0 := by simpa using hu
    have hord : PowerSeries.order (u : PowerSeries ℂ) = (n : ℕ∞) := by
      calc
        PowerSeries.order (u : PowerSeries ℂ) =
            ((PowerSeries.order (u : PowerSeries ℂ)).toNat : ℕ∞) :=
          (PowerSeries.coe_toNat_order hu').symm
        _ = n := by rw [hn]
    exact ⟨u, (PowerSeries.order_eq_nat.mp hord).1,
      (PowerSeries.order_eq_nat.mp hord).2⟩
  · rintro ⟨u, hn, hbelow⟩
    have hu' : (u : PowerSeries ℂ) ≠ 0 := by
      intro hu
      apply hn
      simp [hu]
    have hu : u ≠ 0 := by simpa using hu'
    have hord : PowerSeries.order (u : PowerSeries ℂ) = (n : ℕ∞) :=
      PowerSeries.order_eq_nat.mpr ⟨hn, hbelow⟩
    refine ⟨u, hu, ?_⟩
    rw [hord]
    simp

/-! ## The one-coordinate exact sequence -/

/-- Forget the newest coefficient of an observable prefix. -/
def primeRadialPrefixRestriction
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) :
    PrimeRadialPrefixRange W (N + 1) →ₗ[ℂ] PrimeRadialPrefixRange W N where
  toFun q := ⟨fun j => q.1 j.castSucc, by
    rcases q.2 with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    funext j
    simpa [primeRadialPrefixMap] using congrFun hu j.castSucc⟩
  map_add' q z := by
    apply Subtype.ext
    funext j
    rfl
  map_smul' a q := by
    apply Subtype.ext
    funext j
    rfl

theorem primeRadialPrefixRestriction_surjective
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) :
    Function.Surjective (primeRadialPrefixRestriction W N) := by
  intro q
  rcases q.2 with ⟨u, hu⟩
  let q' : PrimeRadialPrefixRange W (N + 1) :=
    ⟨primeRadialPrefixMap (N + 1) u, ⟨u, rfl⟩⟩
  refine ⟨q', ?_⟩
  apply Subtype.ext
  funext j
  simpa [q', primeRadialPrefixRestriction, primeRadialPrefixMap] using congrFun hu j

/-- The only possible new direction at cutoff `N+1` is its last coordinate. -/
def primeRadialPrefixKernelNewCoordinate
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) :
    LinearMap.ker (primeRadialPrefixRestriction W N) →ₗ[ℂ] ℂ where
  toFun q := q.1.1 (Fin.last N)
  map_add' _q _z := rfl
  map_smul' _a _q := rfl

theorem primeRadialPrefixKernelNewCoordinate_injective
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) :
    Function.Injective (primeRadialPrefixKernelNewCoordinate W N) := by
  intro q z hqz
  apply Subtype.ext
  apply Subtype.ext
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · exact hqz
  · have hqker : primeRadialPrefixRestriction W N q.1 = 0 :=
      LinearMap.mem_ker.mp q.2
    have hzker : primeRadialPrefixRestriction W N z.1 = 0 :=
      LinearMap.mem_ker.mp z.2
    have hq := congrFun (congrArg Subtype.val hqker) i
    have hz := congrFun (congrArg Subtype.val hzker) i
    change q.1.1 i.castSucc = 0 at hq
    change z.1.1 i.castSucc = 0 at hz
    exact hq.trans hz.symm

theorem primeRadialPrefixRestriction_ker_finrank_le_one
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) :
    Module.finrank ℂ (LinearMap.ker (primeRadialPrefixRestriction W N)) ≤ 1 := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (primeRadialPrefixKernelNewCoordinate_injective W N)
  simpa using h

theorem primeRadialPrefixRestriction_ker_nonzero_iff_orderOccurs
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) :
    (∃ q : LinearMap.ker (primeRadialPrefixRestriction W N), q ≠ 0) ↔
      PrimeRadialSubspaceOrderOccurs W (N + 1) := by
  rw [primeRadialSubspaceOrderOccurs_iff_coeff]
  constructor
  · rintro ⟨q, hq⟩
    have hlast : primeRadialPrefixKernelNewCoordinate W N q ≠ 0 := by
      intro hzero
      apply hq
      apply primeRadialPrefixKernelNewCoordinate_injective W N
      simpa using hzero
    rcases q.1.2 with ⟨u, hu⟩
    refine ⟨u, ?_, ?_⟩
    · have hulast := congrFun hu (Fin.last N)
      intro hcoeff
      apply hlast
      change q.1.1 (Fin.last N) = 0
      rw [← hulast]
      simpa [primeRadialPrefixMap] using hcoeff
    · intro i hi
      cases i with
      | zero => exact (u : PrimeRadialProfile).2
      | succ j =>
          have hj : j < N := by omega
          let jf : Fin N := ⟨j, hj⟩
          have hqker : primeRadialPrefixRestriction W N q.1 = 0 :=
            LinearMap.mem_ker.mp q.2
          have hqzero := congrFun (congrArg Subtype.val hqker) jf
          change q.1.1 jf.castSucc = 0 at hqzero
          have hucoord := congrFun hu jf.castSucc
          calc
            PowerSeries.coeff (Nat.succ j) (u : PowerSeries ℂ) =
                q.1.1 jf.castSucc := by
              simpa [jf, primeRadialPrefixMap, Nat.succ_eq_add_one] using hucoord
            _ = 0 := by
              exact hqzero
  · rintro ⟨u, hnew, hbelow⟩
    let q0 : PrimeRadialPrefixRange W (N + 1) :=
      ⟨primeRadialPrefixMap (N + 1) u, ⟨u, rfl⟩⟩
    have hker : primeRadialPrefixRestriction W N q0 = 0 := by
      apply Subtype.ext
      funext j
      change PowerSeries.coeff (j.1 + 1) (u : PowerSeries ℂ) = 0
      exact hbelow _ (by omega)
    let q : LinearMap.ker (primeRadialPrefixRestriction W N) := ⟨q0, hker⟩
    refine ⟨q, ?_⟩
    intro hq
    have hz := congrArg (primeRadialPrefixKernelNewCoordinate W N) hq
    apply hnew
    simpa [q, q0, primeRadialPrefixKernelNewCoordinate, primeRadialPrefixMap] using hz

/-- The binary jump attached to the occurrence of one leading order. -/
noncomputable def primeRadialOrderJump
    (W : Submodule ℂ PrimeRadialProfile) (n : Nat) : Nat := by
  classical
  exact if PrimeRadialSubspaceOrderOccurs W n then 1 else 0

theorem primeRadialOrderJump_eq_one_iff
    (W : Submodule ℂ PrimeRadialProfile) (n : Nat) :
    primeRadialOrderJump W n = 1 ↔ PrimeRadialSubspaceOrderOccurs W n := by
  classical
  simp [primeRadialOrderJump]

theorem primeRadialPrefixRestriction_ker_finrank
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) :
    Module.finrank ℂ (LinearMap.ker (primeRadialPrefixRestriction W N)) =
      primeRadialOrderJump W (N + 1) := by
  classical
  unfold primeRadialOrderJump
  by_cases hoccurs : PrimeRadialSubspaceOrderOccurs W (N + 1)
  · rw [if_pos hoccurs]
    obtain ⟨q, hq⟩ :=
      (primeRadialPrefixRestriction_ker_nonzero_iff_orderOccurs W N).mpr hoccurs
    have hpos : 0 < Module.finrank ℂ
        (LinearMap.ker (primeRadialPrefixRestriction W N)) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨q, hq⟩
    have hle := primeRadialPrefixRestriction_ker_finrank_le_one W N
    omega
  · rw [if_neg hoccurs]
    have hzero : ∀ q : LinearMap.ker (primeRadialPrefixRestriction W N), q = 0 := by
      intro q
      by_contra hq
      exact hoccurs
        ((primeRadialPrefixRestriction_ker_nonzero_iff_orderOccurs W N).mp ⟨q, hq⟩)
    letI : Subsingleton (LinearMap.ker (primeRadialPrefixRestriction W N)) :=
      ⟨fun q z => (hzero q).trans (hzero z).symm⟩
    exact Module.finrank_zero_of_subsingleton

/-- **One-coordinate rank jump.**  Passing from cutoff `N` to `N+1` creates exactly one
observable direction precisely when order `N+1` occurs. -/
theorem primeRadialPrefixRange_finrank_succ
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) :
    Module.finrank ℂ (PrimeRadialPrefixRange W (N + 1)) =
      Module.finrank ℂ (PrimeRadialPrefixRange W N) +
        primeRadialOrderJump W (N + 1) := by
  have hrank :=
    (primeRadialPrefixRestriction W N).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (primeRadialPrefixRestriction_surjective W N),
    finrank_top, primeRadialPrefixRestriction_ker_finrank] at hrank
  exact hrank.symm

/-! ## Exact order census and the Kolchin surface -/

/-- Number of positive leading orders visible through cutoff `N`. -/
noncomputable def primeRadialVisibleOrderCount
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) : Nat :=
  by
    classical
    exact ((Finset.range N).filter fun j =>
      PrimeRadialSubspaceOrderOccurs W (j + 1)).card

theorem primeRadialVisibleOrderCount_succ
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) :
    primeRadialVisibleOrderCount W (N + 1) =
      primeRadialVisibleOrderCount W N +
        primeRadialOrderJump W (N + 1) := by
  classical
  unfold primeRadialOrderJump
  by_cases hoccurs : PrimeRadialSubspaceOrderOccurs W (N + 1) <;>
    simp [primeRadialVisibleOrderCount, Finset.range_add_one,
      Finset.filter_insert, hoccurs]

/-- **Order-census theorem.**  Prefix dimension equals the number of attainable leading orders. -/
theorem primeRadialPrefixRange_finrank_eq_visibleOrderCount
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) :
    Module.finrank ℂ (PrimeRadialPrefixRange W N) =
      primeRadialVisibleOrderCount W N := by
  induction N with
  | zero =>
      have hle := (PrimeRadialPrefixRange W 0).finrank_le
      have hzero : Module.finrank ℂ (PrimeRadialPrefixRange W 0) = 0 := by
        apply Nat.le_zero.mp
        simpa using hle
      simpa [primeRadialVisibleOrderCount] using hzero
  | succ N ih =>
      rw [primeRadialPrefixRange_finrank_succ,
        primeRadialVisibleOrderCount_succ, ih]

theorem primeRadialSubspaceOrderOccurs_toSubmodule_iff
    (A : NonUnitalSubalgebra ℂ PrimeRadialProfile) (n : Nat) :
    PrimeRadialSubspaceOrderOccurs A.toSubmodule n ↔ PrimeRadialOrderOccurs A n :=
  Iff.rfl

/-- **Fusion--Kolchin census law.**  The relative algebraic rank of every cutoff-by-jet rectangle
is the jet depth times the exact number of valuation orders realized by the fusion algebra. -/
theorem primeRadialFusionKolchinRank_eq_orderCount
    (A : NonUnitalSubalgebra ℂ PrimeRadialProfile) (N r : Nat) :
    primeRadialKolchinRank A.toSubmodule N r =
      (r + 1) * primeRadialVisibleOrderCount A.toSubmodule N := by
  rw [primeRadialKolchinRank, primeRadialPrefixRange_finrank_eq_visibleOrderCount]

/-- The exact cutoff derivative of the fusion-field Kolchin surface is one full jet column when
the new valuation order occurs, and zero otherwise. -/
theorem primeRadialFusionKolchinRank_succ
    (A : NonUnitalSubalgebra ℂ PrimeRadialProfile) (N r : Nat) :
    primeRadialKolchinRank A.toSubmodule (N + 1) r =
      primeRadialKolchinRank A.toSubmodule N r +
        (r + 1) * primeRadialOrderJump A.toSubmodule (N + 1) := by
  unfold primeRadialKolchinRank
  rw [primeRadialPrefixRange_finrank_succ, Nat.mul_add]

/-- **Eventual conductor slope law.**  Beyond a finite cutoff, the rank surface gains one entire
jet column exactly at the multiples of its canonical conductor modulus. -/
theorem primeRadialFusionKolchinRank_conductorSlope
    (A : NonUnitalSubalgebra ℂ PrimeRadialProfile) :
    ∃ c : Nat, ∀ N ≥ c, ∀ r : Nat,
      primeRadialKolchinRank A.toSubmodule (N + 1) r =
        primeRadialKolchinRank A.toSubmodule N r +
          if primeRadialConductorModulus A ∣ N + 1 then r + 1 else 0 := by
  obtain ⟨c, hc⟩ := primeRadialOrderOccurs_iff_dvd_eventually A
  refine ⟨c, ?_⟩
  intro N hN r
  rw [primeRadialFusionKolchinRank_succ]
  have hiff := hc (N + 1) (hN.trans (Nat.le_add_right N 1))
  classical
  by_cases hoccurs : PrimeRadialOrderOccurs A (N + 1)
  · have hdvd := hiff.mp hoccurs
    simp [primeRadialOrderJump, primeRadialSubspaceOrderOccurs_toSubmodule_iff,
      hoccurs, hdvd]
  · have hndvd : ¬ primeRadialConductorModulus A ∣ N + 1 :=
      fun hdvd => hoccurs (hiff.mpr hdvd)
    simp [primeRadialOrderJump, primeRadialSubspaceOrderOccurs_toSubmodule_iff,
      hoccurs, hndvd]

/-- Master capstone: the realized finite differential rank, the order census, and the eventual
conductor slope are three exact presentations of one invariant. -/
theorem primeRadialFusion_rankSurfaceLaw
    (A : NonUnitalSubalgebra ℂ PrimeRadialProfile) :
    (∀ N r,
      primeRadialKolchinRank A.toSubmodule N r =
        (r + 1) * primeRadialVisibleOrderCount A.toSubmodule N) ∧
      (∃ c : Nat, ∀ N ≥ c, ∀ r : Nat,
        primeRadialKolchinRank A.toSubmodule (N + 1) r =
          primeRadialKolchinRank A.toSubmodule N r +
            if primeRadialConductorModulus A ∣ N + 1 then r + 1 else 0) := by
  exact ⟨primeRadialFusionKolchinRank_eq_orderCount A,
    primeRadialFusionKolchinRank_conductorSlope A⟩

end

end GaloisForLFunctions.HTGeometry
