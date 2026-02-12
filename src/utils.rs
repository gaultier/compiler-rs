pub(crate) fn round_up(n: usize, rnd: usize) -> usize {
    debug_assert!(rnd.is_power_of_two());
    (n + (rnd - 1)) & !(rnd - 1)
}
