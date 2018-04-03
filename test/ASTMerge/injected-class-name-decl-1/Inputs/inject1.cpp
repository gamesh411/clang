namespace a {
template <typename> struct b;
template <typename> struct c;
template <typename, typename d> using e = d;
class f;
} // namespace a
namespace google {
namespace protobuf {
namespace internal {
class LogMessage {
  LogMessage &operator<<(const char *);
};
} // namespace internal
} // namespace protobuf
} // namespace google
namespace a {
template <typename> class g;
namespace i {
struct h;
template <typename> struct F;
struct G;
template <bool> struct j;
using k = g<int>;
template <typename> struct l {};
} // namespace i
} // namespace a
namespace a {
using n = c<b<i::h>>;
template <typename m> class g : i::F<e<int, i::j<m::p>>> {
  template <typename> friend struct i::l;
};
} // namespace a
namespace a {
using i::G;
}
namespace google {
namespace protobuf {
namespace internal {
LogMessage &LogMessage::operator<<(const char *) { return *this; }
a::f *o;
} // namespace internal
} // namespace protobuf
} // namespace google
