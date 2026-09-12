//! The executable ensemble, and the step that runs on it.
//!
//! `Ensemble` holds machine integers and a `Vec`; `view_of` abstracts it to the
//! ghost `Snapshot` the specification is written over. The obligation each executable
//! function carries is that it computes exactly its specification.
//!
//! ## The clock is ghost
//!
//! Positions are bounded by the perimeter, so they fit comfortably in `i64`. The
//! clock is not bounded — a run goes on for ever — so `Ensemble` does not store it.
//! The step computes `dt` and advances positions; absolute time is carried only in
//! ghost state, where it is an unbounded `int`. That removes the one genuine
//! overflow hazard rather than papering over it.

use vstd::prelude::*;
use crate::dir::Dir;
use crate::snapshot::Snapshot;
use crate::spec::model::*;
use crate::inv::*;

verus! {

/// The perimeter is kept well inside `i64` so that no intermediate can overflow.
/// One unit of the original perimeter is `2*k*n` here, so this is a generous
/// resolution for any realistic team.
pub open spec fn fits(c: Snapshot) -> bool {
    &&& 0 < c.n <= 1_000_000
    &&& 0 < c.k <= 1_000_000
    &&& perimeter(c) <= 1_000_000_000
}

/// A team of drones, executable.
pub struct Ensemble {
    /// The resolution.
    pub k: i64,
    /// Where each drone is, in scaled units.
    pub pos: Vec<i64>,
    /// Which way each drone is heading.
    pub dir: Vec<Dir>,
    /// The clock. Ghost, because it is unbounded — see the module note.
    pub time: Ghost<int>,
}

/// The ghost view of an executable ensemble.
pub open spec fn view_of(e: Ensemble) -> Snapshot {
    Snapshot {
        n: e.pos.len() as int,
        k: e.k as int,
        time: e.time@,
        pos: Seq::new(e.pos.len() as nat, |j: int| e.pos@[j] as int),
        dir: e.dir@,
    }
}

/// What an executable ensemble must satisfy: the representation is faithful, the
/// standing invariant holds of its view, and the numbers fit.
///
/// The invariant is part of this rather than an extra hypothesis because the
/// position bounds are exactly what rules out overflow — a drone on the perimeter
/// is a drone whose coordinate fits.
pub open spec fn repr_ok(e: Ensemble) -> bool {
    &&& e.pos.len() == e.dir.len()
    &&& e.k > 0
    &&& inv(view_of(e))
    &&& fits(view_of(e))
}

/// The perimeter, computed, with its bound.
pub fn perimeter_ex(e: &Ensemble) -> (r: i64)
    requires repr_ok(*e)
    ensures r as int == perimeter(view_of(*e)), 0 <= r <= 1_000_000_000
{
    2 * e.k * (e.pos.len() as i64)
}

pub proof fn lemma_view_pos(e: Ensemble, i: int)
    requires 0 <= i < e.pos.len()
    ensures view_of(e).pos[i] == e.pos@[i] as int
{
}

/// `border_time`, computed.
pub fn border_time_ex(e: &Ensemble, i: usize) -> (r: i64)
    requires repr_ok(*e), 0 <= i < e.pos.len()
    ensures r as int == border_time(view_of(*e), i as int)
{
    proof { lemma_view_pos(*e, i as int); }
    let perim = perimeter_ex(e);
    assert(0 <= view_of(*e).pos[i as int] <= perimeter(view_of(*e)));
    if e.dir[i] == Dir::Left {
        e.pos[i]
    } else {
        perim - e.pos[i]
    }
}

/// `gap`, computed.
pub fn gap_ex(e: &Ensemble, i: usize) -> (r: i64)
    requires repr_ok(*e), 0 <= i, i + 1 < e.pos.len()
    ensures r as int == gap(view_of(*e), i as int)
{
    proof {
        lemma_view_pos(*e, i as int);
        lemma_view_pos(*e, i as int + 1);
    }
    assert(0 <= view_of(*e).pos[i as int] <= perimeter(view_of(*e)));
    assert(0 <= view_of(*e).pos[i as int + 1] <= perimeter(view_of(*e)));
    e.pos[i + 1] - e.pos[i]
}

/// `meet_time`, computed.
pub fn meet_time_ex(e: &Ensemble, i: usize) -> (r: i64)
    requires repr_ok(*e), 0 <= i, i + 1 < e.pos.len()
    ensures r as int == meet_time(view_of(*e), i as int)
{
    let g = gap_ex(e, i);
    // the gap is nonnegative and even, so Rust's truncating division and the
    // specification's agree -- there is no convention to get wrong here
    assert(0 <= gap(view_of(*e), i as int));
    g / 2
}

/// `separation_time`, computed.
pub fn separation_time_ex(e: &Ensemble, i: usize) -> (r: i64)
    requires repr_ok(*e), 0 <= i < e.pos.len()
    ensures r as int == separation_time(view_of(*e), i as int)
{
    proof { lemma_view_pos(*e, i as int); }
    let perim = perimeter_ex(e);
    // the bound must be established before the arithmetic, not after it
    proof { crate::geometry::lemma_common_le_perimeter(view_of(*e), i as int); }
    let ce: i64 = 2 * e.k * ((i as i64) + 1);
    assert(ce as int == common_end(view_of(*e), i as int));
    assert(0 <= view_of(*e).pos[i as int] <= perimeter(view_of(*e)));
    if e.dir[i] == Dir::Left {
        e.pos[i] - ce
    } else {
        ce - e.pos[i]
    }
}

/// `co_located`, computed.
pub fn co_located_ex(e: &Ensemble, i: usize) -> (r: bool)
    requires repr_ok(*e), 0 <= i, i + 1 < e.pos.len()
    ensures r == co_located(view_of(*e), i as int)
{
    gap_ex(e, i) == 0
}

/// `approaching`, computed.
pub fn approaching_ex(e: &Ensemble, i: usize) -> (r: bool)
    requires repr_ok(*e), 0 <= i, i + 1 < e.pos.len()
    ensures r == approaching(view_of(*e), i as int)
{
    e.dir[i] == Dir::Right && e.dir[i + 1] == Dir::Left
}

/// `escorting`, computed.
pub fn escorting_ex(e: &Ensemble, i: usize) -> (r: bool)
    requires repr_ok(*e), 0 <= i, i + 1 < e.pos.len()
    ensures r == escorting(view_of(*e), i as int)
{
    co_located_ex(e, i) && e.dir[i] == e.dir[i + 1]
}

/// `at_separation`, computed.
pub fn at_separation_ex(e: &Ensemble, i: usize) -> (r: bool)
    requires repr_ok(*e), 0 <= i, i + 1 < e.pos.len()
    ensures r == at_separation(view_of(*e), i as int)
{
    proof {
        lemma_view_pos(*e, i as int);
        crate::geometry::lemma_common_le_perimeter(view_of(*e), i as int);
    }
    let ce: i64 = 2 * e.k * ((i as i64) + 1);
    co_located_ex(e, i) && e.pos[i] == ce
}

/// `at_left_border`, computed.
pub fn at_left_border_ex(e: &Ensemble, i: usize) -> (r: bool)
    requires repr_ok(*e), 0 <= i < e.pos.len()
    ensures r == at_left_border(view_of(*e), i as int)
{
    proof { lemma_view_pos(*e, i as int); }
    e.pos[i] == 0 && e.dir[i] == Dir::Left
}

/// `at_right_border`, computed.
pub fn at_right_border_ex(e: &Ensemble, i: usize) -> (r: bool)
    requires repr_ok(*e), 0 <= i < e.pos.len()
    ensures r == at_right_border(view_of(*e), i as int)
{
    proof { lemma_view_pos(*e, i as int); }
    let perim = perimeter_ex(e);
    e.pos[i] == perim && e.dir[i] == Dir::Right
}

/// `sep_right`, computed.
pub fn sep_right_ex(e: &Ensemble, i: usize) -> (r: bool)
    requires repr_ok(*e), 0 <= i < e.pos.len()
    ensures r == sep_right(view_of(*e), i as int)
{
    if i + 1 < e.pos.len() { at_separation_ex(e, i) } else { false }
}

/// `sep_left`, computed.
pub fn sep_left_ex(e: &Ensemble, i: usize) -> (r: bool)
    requires repr_ok(*e), 0 <= i < e.pos.len()
    ensures r == sep_left(view_of(*e), i as int)
{
    if i > 0 { at_separation_ex(e, i - 1) } else { false }
}

/// `meet_right`, computed.
pub fn meet_right_ex(e: &Ensemble, i: usize) -> (r: bool)
    requires repr_ok(*e), 0 <= i < e.pos.len()
    ensures r == meet_right(view_of(*e), i as int)
{
    if i + 1 < e.pos.len() { co_located_ex(e, i) && approaching_ex(e, i) } else { false }
}

/// `meet_left`, computed.
pub fn meet_left_ex(e: &Ensemble, i: usize) -> (r: bool)
    requires repr_ok(*e), 0 <= i < e.pos.len()
    ensures r == meet_left(view_of(*e), i as int)
{
    if i > 0 { co_located_ex(e, i - 1) && approaching_ex(e, i - 1) } else { false }
}

/// `escort_dir`, computed.
pub fn escort_dir_ex(e: &Ensemble, i: usize) -> (r: Dir)
    requires repr_ok(*e), 0 <= i < e.pos.len()
    ensures r == escort_dir(view_of(*e), i as int)
{
    proof {
        lemma_view_pos(*e, i as int);
        crate::geometry::lemma_common_le_perimeter(view_of(*e), i as int);
    }
    let ce: i64 = 2 * e.k * ((i as i64) + 1);
    if e.pos[i] < ce { Dir::Right } else { Dir::Left }
}

/// `escort_dir_left`, computed.
pub fn escort_dir_left_ex(e: &Ensemble, i: usize) -> (r: Dir)
    requires repr_ok(*e), 0 <= i < e.pos.len()
    ensures r == escort_dir_left(view_of(*e), i as int)
{
    proof {
        lemma_view_pos(*e, i as int);
        crate::geometry::lemma_left_end_nonneg(view_of(*e), i as int);
        crate::geometry::lemma_common_le_perimeter(view_of(*e), i as int);
        crate::geometry::lemma_segment_width(view_of(*e), i as int);
    }
    let le: i64 = 2 * e.k * (i as i64);
    if e.pos[i] < le { Dir::Right } else { Dir::Left }
}

/// **The heading update, computed** — Algorithm A's priority order.
pub fn new_dir_ex(e: &Ensemble, i: usize) -> (r: Dir)
    requires repr_ok(*e), 0 <= i < e.pos.len()
    ensures r == new_dir(view_of(*e), i as int)
{
    if at_left_border_ex(e, i) {
        Dir::Right
    } else if at_right_border_ex(e, i) {
        Dir::Left
    } else if sep_right_ex(e, i) {
        Dir::Left
    } else if sep_left_ex(e, i) {
        Dir::Right
    } else if meet_right_ex(e, i) {
        escort_dir_ex(e, i)
    } else if meet_left_ex(e, i) {
        escort_dir_left_ex(e, i)
    } else {
        e.dir[i]
    }
}

/// `drone_next_time`, computed.
pub fn drone_next_time_ex(e: &Ensemble, i: usize) -> (r: i64)
    requires repr_ok(*e), 0 <= i < e.pos.len()
    ensures
        r as int == drone_next_time(view_of(*e), i as int),
        0 <= r <= 1_000_000_000,
{
    proof {
        crate::schedule::lemma_drone_next_time_nonneg(view_of(*e), i as int);
        crate::schedule::lemma_drone_le_border(view_of(*e), i as int);
    }
    let b = border_time_ex(e, i);
    if i + 1 < e.pos.len() {
        if approaching_ex(e, i) {
            let m = meet_time_ex(e, i);
            if b < m { b } else { m }
        } else if escorting_ex(e, i) {
            let sp = separation_time_ex(e, i);
            if b < sp { b } else { sp }
        } else {
            b
        }
    } else {
        b
    }
}

/// **The step length, computed** — the earliest deadline across the team.
///
/// `min_deadline` is written as a recursion in the specification; this is the loop
/// that computes it, and the invariant is the correspondence between them.
pub fn time_to_next_event_ex(e: &Ensemble) -> (r: i64)
    requires repr_ok(*e)
    ensures
        r as int == time_to_next_event(view_of(*e)),
        0 <= r <= 1_000_000_000,
{
    let n = e.pos.len();
    let mut best = drone_next_time_ex(e, 0);
    let mut m: usize = 1;
    while m < n
        invariant
            1 <= m <= n,
            n == e.pos.len(),
            repr_ok(*e),
            best as int == min_deadline(view_of(*e), m as int),
            0 <= best <= 1_000_000_000,
        decreases n - m
    {
        let d = drone_next_time_ex(e, m);
        if d < best {
            best = d;
        }
        m = m + 1;
    }
    best
}

/// **One step of the system, executed — and proved to be *the* step.**
///
/// This is the obligation the whole crate exists to discharge: the executable
/// ensemble ends up in exactly the configuration the specification says it should,
/// with both standing conditions intact and no arithmetic overflow anywhere.
///
/// The clock is advanced first, so that once the drones have flown the ensemble's
/// view is exactly `flown(c0)` — which is the configuration the headings must be
/// computed from. Getting that order wrong is the off-by-one `Dpss/NonZeno.lean`
/// warns about.
pub fn step_ex(e: &mut Ensemble)
    requires
        repr_ok(*old(e)),
        apart_on_boundaries(view_of(*old(e))),
    ensures
        repr_ok(*final(e)),
        apart_on_boundaries(view_of(*final(e))),
        view_of(*final(e)) == spec_step(view_of(*old(e))),
{
    let ghost c0 = view_of(*old(e));
    proof {
        crate::step_lemmas::lemma_inv_flown(c0);
        crate::step_lemmas::lemma_inv_step(c0);
        crate::reachable::lemma_apart_on_boundaries_step(c0);
    }
    let dt = time_to_next_event_ex(e);
    let n = e.pos.len();
    e.time = Ghost(c0.time + dt as int);

    // fly to the next event
    let mut j: usize = 0;
    while j < n
        invariant
            0 <= j <= n,
            n == e.pos.len(),
            e.pos.len() == e.dir.len(),
            e.dir@ == c0.dir,
            e.k as int == c0.k,
            e.time@ == c0.time + dt as int,
            dt as int == time_to_next_event(c0),
            inv(c0),
            fits(c0),
            inv(flown(c0)),
            forall|t: int| 0 <= t < j ==> #[trigger] e.pos@[t] as int == flown(c0).pos[t],
            forall|t: int| j <= t < n ==> #[trigger] e.pos@[t] as int == c0.pos[t],
        decreases n - j
    {
        proof {
            assert(0 <= flown(c0).pos[j as int] <= perimeter(flown(c0)));
            assert(flown(c0).pos[j as int]
                == c0.pos[j as int] + isign(c0.dir[j as int]) * dt as int);
        }
        let s: i64 = if e.dir[j] == Dir::Left { -1 } else { 1 };
        let v = e.pos[j] + s * dt;
        e.pos.set(j, v);
        j = j + 1;
    }
    // struct equality is field-by-field; only the sequences need extensionality
    assert(view_of(*e).pos =~= flown(c0).pos);
    assert(view_of(*e).dir =~= flown(c0).dir);
    assert(view_of(*e) == flown(c0));

    // then let every due event fire
    let mut nd: Vec<Dir> = Vec::new();
    let mut m: usize = 0;
    while m < n
        invariant
            0 <= m <= n,
            n == e.pos.len(),
            view_of(*e) == flown(c0),
            repr_ok(*e),
            nd.len() == m,
            forall|t: int| 0 <= t < m ==> #[trigger] nd@[t] == new_dir(flown(c0), t),
        decreases n - m
    {
        let d = new_dir_ex(e, m);
        nd.push(d);
        m = m + 1;
    }
    e.dir = nd;
    assert(view_of(*e).pos =~= spec_step(c0).pos);
    assert(view_of(*e).dir =~= spec_step(c0).dir);
    assert(view_of(*e) == spec_step(c0));
}

/// **A run, executed** — and proved to be *the* run.
///
/// `Dpss/IntModel.lean`, `DPSS.IntConfig.run`.
pub fn run_ex(e: &mut Ensemble, steps: usize)
    requires
        repr_ok(*old(e)),
        apart_on_boundaries(view_of(*old(e))),
    ensures
        repr_ok(*final(e)),
        apart_on_boundaries(view_of(*final(e))),
        view_of(*final(e)) == spec_run(view_of(*old(e)), steps as nat),
{
    let ghost c0 = view_of(*old(e));
    let mut t: usize = 0;
    while t < steps
        invariant
            0 <= t <= steps,
            repr_ok(*e),
            apart_on_boundaries(view_of(*e)),
            view_of(*e) == spec_run(c0, t as nat),
        decreases steps - t
    {
        step_ex(e);
        t = t + 1;
    }
}

// ---------------------------------------------------------------------------
// The standing conditions, executed (S7b)
//
// `on_perimeter`, `adj_ordered`, `escorts_coherent` and `on_lattice` are the
// four definitions `scripts/lean_to_verus.py` refuses to translate -- they
// quantify over `Fin n` with a dependent proof argument -- so they are
// hand-written transcriptions of `Dpss/IntModel.lean`. Being `spec fn`s they
// never execute, so no trace could exercise them either, and nothing checked
// them against the Lean at all. That is the same hole S6b closed for the fence
// and the link, and these close it for the team.
//
// The point of these is that they must be evaluable on states that *violate*
// them. So none may require `repr_ok`: `repr_ok` contains `inv`, which would
// make the answer `true` by assumption and the whole exercise vacuous. They
// require only as much as their arithmetic needs -- `repr_wf` to compute a
// perimeter, and the position bounds to subtract two positions without
// overflowing, which `on_perimeter_ex` itself is what establishes.
// ---------------------------------------------------------------------------

/// The representation alone: faithful and non-overflowing, with **nothing**
/// assumed about the standing conditions. `repr_ok` is exactly this plus `inv`.
pub open spec fn repr_wf(e: Ensemble) -> bool {
    &&& e.pos.len() == e.dir.len()
    &&& e.k > 0
    &&& fits(view_of(e))
}

/// `repr_wf` plus the position bounds — what `on_perimeter_ex` establishes, and
/// exactly what the other three need to form a gap without overflowing.
pub open spec fn repr_bounded(e: Ensemble) -> bool {
    &&& repr_wf(e)
    &&& on_perimeter(view_of(e))
}

/// The perimeter, from a merely well-formed ensemble. `perimeter_ex` needs
/// `repr_ok`; this one cannot.
pub fn perimeter_wf_ex(e: &Ensemble) -> (r: i64)
    requires repr_wf(*e)
    ensures r as int == perimeter(view_of(*e)), 0 <= r <= 1_000_000_000
{
    2 * e.k * (e.pos.len() as i64)
}

/// `on_perimeter`, computed.
pub fn on_perimeter_ex(e: &Ensemble) -> (r: bool)
    requires repr_wf(*e)
    ensures r == on_perimeter(view_of(*e))
{
    let n = e.pos.len();
    let perim = perimeter_wf_ex(e);
    let mut j: usize = 0;
    let mut ok: bool = true;
    while j < n
        invariant
            0 <= j <= n,
            n == e.pos.len(),
            repr_wf(*e),
            perim as int == perimeter(view_of(*e)),
            ok == (forall|i: int| 0 <= i < j ==>
                0 <= #[trigger] view_of(*e).pos[i] <= perimeter(view_of(*e))),
        decreases n - j
    {
        proof { lemma_view_pos(*e, j as int); }
        if e.pos[j] < 0 || e.pos[j] > perim {
            ok = false;
        }
        j = j + 1;
    }
    ok
}

/// `adj_ordered`, computed.
pub fn adj_ordered_ex(e: &Ensemble) -> (r: bool)
    requires repr_bounded(*e)
    ensures r == adj_ordered(view_of(*e))
{
    let n = e.pos.len();
    let mut j: usize = 0;
    let mut ok: bool = true;
    while j + 1 < n
        invariant
            0 <= j < n,
            n == e.pos.len(),
            repr_bounded(*e),
            ok == (forall|i: int| 0 <= i < j ==> 0 <= #[trigger] gap(view_of(*e), i)),
        decreases n - j
    {
        proof {
            lemma_view_pos(*e, j as int);
            lemma_view_pos(*e, j as int + 1);
        }
        assert(0 <= view_of(*e).pos[j as int] <= perimeter(view_of(*e)));
        assert(0 <= view_of(*e).pos[j as int + 1] <= perimeter(view_of(*e)));
        let g: i64 = e.pos[j + 1] - e.pos[j];
        assert(g as int == gap(view_of(*e), j as int));
        if g < 0 {
            ok = false;
        }
        j = j + 1;
    }
    ok
}

/// `on_lattice`, computed.
///
/// The parity is read off the two positions rather than off the gap, because
/// both positions are nonnegative and Rust's truncating `%` agrees with the
/// specification's Euclidean one there. On the gap, which may be negative, they
/// would not agree, and the check would be wrong for exactly the states it is
/// meant to reject.
pub fn on_lattice_ex(e: &Ensemble) -> (r: bool)
    requires repr_bounded(*e)
    ensures r == on_lattice(view_of(*e))
{
    let n = e.pos.len();
    let mut j: usize = 0;
    let mut ok: bool = true;
    while j + 1 < n
        invariant
            0 <= j < n,
            n == e.pos.len(),
            repr_bounded(*e),
            ok == (forall|i: int| 0 <= i < j ==> #[trigger] gap(view_of(*e), i) % 2 == 0),
        decreases n - j
    {
        proof {
            lemma_view_pos(*e, j as int);
            lemma_view_pos(*e, j as int + 1);
        }
        assert(0 <= view_of(*e).pos[j as int] <= perimeter(view_of(*e)));
        assert(0 <= view_of(*e).pos[j as int + 1] <= perimeter(view_of(*e)));
        assert((view_of(*e).pos[j as int + 1] - view_of(*e).pos[j as int]) % 2 == 0
            <==> view_of(*e).pos[j as int] % 2 == view_of(*e).pos[j as int + 1] % 2);
        let even: bool = e.pos[j] % 2 == e.pos[j + 1] % 2;
        assert(even == (gap(view_of(*e), j as int) % 2 == 0));
        if !even {
            ok = false;
        }
        j = j + 1;
    }
    ok
}

/// `escorts_coherent`, computed.
pub fn escorts_coherent_ex(e: &Ensemble) -> (r: bool)
    requires repr_bounded(*e)
    ensures r == escorts_coherent(view_of(*e))
{
    let n = e.pos.len();
    let mut j: usize = 0;
    let mut ok: bool = true;
    while j + 1 < n
        invariant
            0 <= j < n,
            n == e.pos.len(),
            repr_bounded(*e),
            ok == (forall|i: int| 0 <= i && i < j && #[trigger] escorting(view_of(*e), i)
                ==> 0 <= separation_time(view_of(*e), i)),
        decreases n - j
    {
        proof {
            lemma_view_pos(*e, j as int);
            lemma_view_pos(*e, j as int + 1);
            crate::geometry::lemma_common_le_perimeter(view_of(*e), j as int);
        }
        assert(0 <= view_of(*e).pos[j as int] <= perimeter(view_of(*e)));
        assert(0 <= view_of(*e).pos[j as int + 1] <= perimeter(view_of(*e)));
        let ce: i64 = 2 * e.k * ((j as i64) + 1);
        assert(ce as int == common_end(view_of(*e), j as int));
        let esc: bool = e.pos[j + 1] - e.pos[j] == 0 && e.dir[j] == e.dir[j + 1];
        assert(esc == escorting(view_of(*e), j as int));
        // the match, not an `if`, so that Verus case-splits `isign` on the variant
        let st: i64 = match e.dir[j] {
            Dir::Left => e.pos[j] - ce,
            Dir::Right => ce - e.pos[j],
        };
        assert(st as int == separation_time(view_of(*e), j as int));
        if esc && st < 0 {
            ok = false;
        }
        j = j + 1;
    }
    ok
}

/// The whole standing invariant, computed.
///
/// The order is not cosmetic: `on_perimeter` is checked first because the other
/// three need its bounds before they may subtract two positions.
pub fn inv_ex(e: &Ensemble) -> (r: bool)
    requires repr_wf(*e)
    ensures r == inv(view_of(*e))
{
    if !on_perimeter_ex(e) {
        return false;
    }
    adj_ordered_ex(e) && escorts_coherent_ex(e) && on_lattice_ex(e)
}

/// `apart_on_boundaries`, computed — the reachability invariant carried
/// alongside `inv`, and the other half of `step_ex`'s precondition.
pub fn apart_on_boundaries_ex(e: &Ensemble) -> (r: bool)
    requires repr_bounded(*e)
    ensures r == apart_on_boundaries(view_of(*e))
{
    let n = e.pos.len();
    let mut j: usize = 0;
    let mut ok: bool = true;
    while j + 1 < n
        invariant
            0 <= j < n,
            n == e.pos.len(),
            repr_bounded(*e),
            ok == (forall|i: int| 0 <= i && i < j && #[trigger] co_located(view_of(*e), i)
                && view_of(*e).dir[i] == Dir::Left && view_of(*e).dir[i + 1] == Dir::Right
                ==> view_of(*e).pos[i] == common_end(view_of(*e), i)),
        decreases n - j
    {
        proof {
            lemma_view_pos(*e, j as int);
            lemma_view_pos(*e, j as int + 1);
            crate::geometry::lemma_common_le_perimeter(view_of(*e), j as int);
        }
        assert(0 <= view_of(*e).pos[j as int] <= perimeter(view_of(*e)));
        assert(0 <= view_of(*e).pos[j as int + 1] <= perimeter(view_of(*e)));
        let ce: i64 = 2 * e.k * ((j as i64) + 1);
        assert(ce as int == common_end(view_of(*e), j as int));
        let bad: bool = e.pos[j + 1] - e.pos[j] == 0
            && e.dir[j] == Dir::Left && e.dir[j + 1] == Dir::Right;
        assert(bad == (co_located(view_of(*e), j as int)
            && view_of(*e).dir[j as int] == Dir::Left
            && view_of(*e).dir[j as int + 1] == Dir::Right));
        if bad && e.pos[j] != ce {
            ok = false;
        }
        j = j + 1;
    }
    ok
}

} // verus!
